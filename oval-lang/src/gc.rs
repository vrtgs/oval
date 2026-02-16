use crate::abort::AbortGuard;
use crate::hashed::HashSet;
use crate::mutex::Mutex;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use cfg_if::cfg_if;
use core::alloc::Layout;
use core::fmt::{Debug, Formatter};
use core::marker::PhantomData;
use core::mem;
use core::num::NonZero;
use core::ops::Deref;
use core::ptr::NonNull;
use core::sync::atomic::Ordering;

cfg_if! {
    // See note for HandleInt in the top of crate::arena
    if #[cfg(target_pointer_width = "16")] {
        type RefCounter = portable_atomic::AtomicU16;
        type RefCountInner = u16;
    } else {
        type RefCounter = portable_atomic::AtomicU32;
        type RefCountInner = u32;
    }
}

enum Opaque {}

struct Tracer {
    trace_stack: Vec<NonNull<ObjectFooter>>,
}

impl Tracer {
    unsafe fn add(&mut self, obj: NonNull<ObjectFooter>) {
        self.trace_stack.push(obj)
    }
}


struct ObjectVtable {
    trace: unsafe fn(*const Opaque, &mut Tracer),
    finalize: unsafe fn(*mut Opaque)
}

/// # Safety
/// TODO document safety
pub unsafe trait Trace {
    fn trace(&self, add: impl FnMut(NonNull<ObjectFooter>));
}

macro_rules! impl_empty_trace {
    ($($ty: ty)+) => {
        $(unsafe impl Trace for $ty {
            fn trace(&self, _add: impl FnMut(NonNull<ObjectFooter>)) {}
        })+
    };
}

impl_empty_trace! {
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize

    f32 f64

    str

    String
}

unsafe impl<T: Trace> Trace for [T] {
    fn trace(&self, mut add: impl FnMut(NonNull<ObjectFooter>)) {
        for item in self {
            T::trace(item, &mut add)
        }
    }
}

unsafe impl<T: Trace, const N: usize> Trace for [T; N] {
    fn trace(&self, add: impl FnMut(NonNull<ObjectFooter>)) {
        <[T]>::trace(self, add)
    }
}

unsafe impl<T: Trace> Trace for Vec<T> {
    fn trace(&self, add: impl FnMut(NonNull<ObjectFooter>)) {
        <[T]>::trace(self, add)
    }
}

unsafe impl<T: ?Sized + Trace> Trace for Box<T> {
    fn trace(&self, add: impl FnMut(NonNull<ObjectFooter>)) {
        <T>::trace(self, add)
    }
}

unsafe impl<T: Trace> Trace for GcRef<'_, T> {
    fn trace(&self, mut add: impl FnMut(NonNull<ObjectFooter>)) {
        unsafe { add(NonNull::new_unchecked(&raw mut (*self.as_raw_ptr()).footer)) }
        <T>::trace(self, add)
    }
}

unsafe fn finalize<T>(ptr: *mut Opaque) {
    unsafe { core::ptr::drop_in_place::<T>(ptr.cast::<T>()) }
}

unsafe fn trace<T: Trace>(ptr: *const Opaque, tracer: &mut Tracer) {
    unsafe { T::trace(&*(ptr.cast::<T>()), move |ptr| tracer.add(ptr)) }
}


#[repr(C)]
pub struct ObjectFooter {
    offset_bytes: NonZero<usize>,
    // stored as n where align = 2^n
    object_alignment: u8,
    // store type info to be able to get back the layout and finalize info and tracing
    vtable: &'static ObjectVtable,
    ref_count: RefCounter,
}

unsafe impl Send for ObjectFooter {}
unsafe impl Sync for ObjectFooter {}

#[repr(C)]
struct Object<T = Opaque> {
    obj_data: T,
    footer: ObjectFooter,
}

impl ObjectFooter {
    unsafe fn inc_ref(this: *const Self) {
        // Using a relaxed ordering is alright here, as knowledge of the
        // original reference prevents other threads from erroneously deleting
        // the object.
        let counter = unsafe { &(*this).ref_count };
        let mut last_val = counter.load(Ordering::Relaxed);
        let cas = |old, new| {
            counter.compare_exchange_weak(
                old,
                new,
                Ordering::Relaxed,
                Ordering::Relaxed
            )
        };
        while last_val != RefCountInner::MAX {
            let new = unsafe { last_val.unchecked_add(1) };
            let Err(actual) = cas(last_val, new) else {
                break;
            };
            last_val = actual
        }
    }

    unsafe fn dec_ref(this: *mut Self) {
        let this_ref = unsafe { &*this };
        let counter = &this_ref.ref_count;
        let mut last_val = counter.load(Ordering::Relaxed);
        let cas = |old, new| {
            counter.compare_exchange_weak(
                old,
                new,
                Ordering::AcqRel,
                Ordering::Relaxed
            )
        };
        let hit_zero = loop {
            if last_val == RefCountInner::MAX {
                return;
            }
            debug_assert_ne!(last_val, 0, "use after free");
            let new = unsafe { last_val.unchecked_sub(1) };
            let Err(actual) = cas(last_val, new) else {
                break new == 0
            };
            last_val = actual;
        };

        if hit_zero {
            unsafe {
                let obj_ptr = this
                    .byte_sub(this_ref.offset_bytes.get())
                    .cast::<Opaque>();
                (this_ref.vtable.finalize)(obj_ptr)
            }
        }
    }
}


#[repr(transparent)]
pub struct GcRef<'gc, T = Opaque>(NonNull<Object<T>>, PhantomData<&'gc GcInner>);

impl<T> GcRef<'_, T> {
    #[inline(always)]
    pub const fn into_ptr(self) -> NonNull<Object<T>> {
        let ptr = self.0;
        mem::forget(self);
        ptr
    }

    #[inline(always)]
    pub const fn as_ptr(&self) -> NonNull<Object<T>> {
        self.0
    }

    #[inline(always)]
    pub const fn as_raw_ptr(&self) -> *mut Object<T> {
        self.0.as_ptr()
    }

    #[inline(always)]
    pub const fn get_ref(&self) -> &T {
        unsafe { &((*self.0.as_ptr()).obj_data) }
    }
}

unsafe impl<T: Send + Sync> Send for GcRef<'_, T> {}
unsafe impl<T: Send + Sync> Sync for GcRef<'_, T> {}

impl<T> Drop for GcRef<'_, T> {
    fn drop(&mut self) {
        unsafe { ObjectFooter::dec_ref(&raw mut (*self.0.as_ptr()).footer) }
    }
}

impl<T> Clone for GcRef<'_, T> {
    fn clone(&self) -> Self {
        unsafe { ObjectFooter::inc_ref(&raw const (*self.0.as_ptr()).footer) }
        Self(self.as_ptr(), PhantomData)
    }
}

impl<T> Deref for GcRef<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.get_ref()
    }
}

struct DeallocGuard {
    ptr: NonNull<Object>,
    layout: Layout,
    vtable: Option<&'static ObjectVtable>,
}

impl Drop for DeallocGuard {
    fn drop(&mut self) {
        unsafe {
            if let Some(table) = self.vtable {
                (table.finalize)(&raw mut (*self.ptr.as_ptr()).obj_data)
            }
            alloc::alloc::dealloc(self.ptr.as_ptr().cast::<u8>(), self.layout)
        }
    }
}

struct ObjectTracker {
    objects: HashSet<NonNull<ObjectFooter>>,
}

impl ObjectTracker {
    unsafe fn free(&mut self, ptr: NonNull<ObjectFooter>) {
        unsafe {
            let footer_ref = ptr.as_ref();
            let is_live = footer_ref.ref_count.load(Ordering::Release) != 0;
            let offset = footer_ref.offset_bytes.get();
            let obj_start = ptr
                .byte_sub(offset)
                .cast::<Object>();
            let alignment = 1_usize.unchecked_shl(footer_ref.object_alignment as u32);
            let layout = Layout::from_size_align_unchecked(
                offset.unchecked_add(size_of::<ObjectFooter>()),
                alignment
            ).pad_to_align();

            let guard = AbortGuard::new();
            let removed = self.objects.remove(&ptr);
            core::hint::assert_unchecked(removed);
            guard.disarm();
            drop(DeallocGuard {
                ptr: obj_start,
                layout,
                vtable: is_live.then_some(footer_ref.vtable)
            });
        }
    }

    unsafe fn alloc(
        &mut self,
        data: Layout,
        fill: impl FnOnce(NonNull<Object>),
        vtable: &'static ObjectVtable,
    ) -> NonNull<Object> {
        unsafe {
            core::hint::assert_unchecked(data.size() != 0);

            let (obj_layout, footer_offset) = match data.extend(Layout::new::<ObjectFooter>()) {
                Ok((layout, offset)) => (
                    layout.pad_to_align(),
                    // since data is not a zst the offset can't be zero
                    NonZero::new_unchecked(offset)
                ),
                Err(_) => alloc::alloc::handle_alloc_error(data)
            };

            let alloc_ptr = match NonNull::new(alloc::alloc::alloc(obj_layout)) {
                Some(ptr) => ptr.cast::<Object>(),
                None => alloc::alloc::handle_alloc_error(obj_layout)
            };

            let mut guard = DeallocGuard {
                ptr: alloc_ptr,
                layout: obj_layout,
                vtable: None
            };

            let footer_ptr = alloc_ptr
                .byte_add(footer_offset.get())
                .cast::<ObjectFooter>();

            const { assert!(usize::BITS < u8::MAX as u32) }

            let alignment = NonZero::new_unchecked(obj_layout.align()).ilog2() as u8;
            footer_ptr.write(ObjectFooter {
                offset_bytes: footer_offset,
                object_alignment: alignment,
                vtable,
                ref_count: RefCounter::new(1),
            });

            fill(alloc_ptr);
            // drop if panic occurs after this point
            guard.vtable = Some(vtable);

            self.objects.insert_unique_unchecked(footer_ptr);
            mem::forget(guard);
            alloc_ptr
        }
    }
}

struct GcInner {
    ty_info: (),
    allocator: Mutex<ObjectTracker>,
}

impl GcInner {
    unsafe fn alloc_obj<'a, T>(
        this: NonNull<Self>,
        make_obj: impl FnOnce() -> T,
        vtable: &'static ObjectVtable
    ) -> GcRef<'a, T> {
        let this_ref: &'a Self = unsafe { this.as_ref() };
        // TODO add finalize and trace so inner data isn't leaked and can also be collected
        let ptr: NonNull<Object> = unsafe {
            this_ref.allocator.lock().alloc(
                Layout::new::<T>(),
                |ptr| {
                    let obj = make_obj();
                    ptr.cast::<T>().write(obj)
                },
                vtable
            )
        };
        GcRef(ptr.cast::<Object<T>>(), PhantomData)
    }

    unsafe fn collect(&self, roots: &mut dyn Iterator<Item=NonNull<ObjectFooter>>) {
        let alloc = &mut *self.allocator.lock();
        let mut live_pointers = HashSet::with_capacity_and_hasher(
            alloc.objects.len(),
            crate::hashed::Hasher::default()
        );
        live_pointers.extend(roots);

        let mut tracer = Tracer {
            trace_stack: Vec::with_capacity(
                live_pointers.len().saturating_add(live_pointers.len() / 2)
            )
        };

        let trace = |
            obj: NonNull<ObjectFooter>,
            tracer: &mut Tracer
        | unsafe {
            let footer_ref = obj.as_ref();
            let obj_ptr = obj
                .byte_sub(footer_ref.offset_bytes.get())
                .cast::<Opaque>()
                .as_ptr();

            (footer_ref.vtable.trace)(obj_ptr, tracer)
        };

        for &root in &live_pointers {
            trace(root, &mut tracer)
        }

        while let Some(ptr) = tracer.trace_stack.pop() {
            if live_pointers.insert(ptr) {
                trace(ptr, &mut tracer)
            }
        }

        let unalive_pointers = alloc
            .objects
            .difference(&live_pointers)
            .copied()
            .collect::<Vec<_>>();

        for garbage in unalive_pointers {
            unsafe { alloc.free(garbage) }
        }
    }
}

#[derive(Clone)]
pub struct GcHandle(Arc<GcInner>);


impl GcHandle {
    pub fn alloc<T: Trace>(&self, obj: T) -> GcRef<'_, T> {
        unsafe {
            GcInner::alloc_obj(
                NonNull::<GcInner>::from_ref(&self.0),
                move || obj,
                &ObjectVtable {
                    trace: trace::<T>,
                    finalize: finalize::<T>,
                }
            )
        }
    }

    pub unsafe fn collect(&self, roots: impl Iterator<Item=NonNull<ObjectFooter>>) {
        unsafe { self.0.collect(&mut { roots }) }
    }
}

impl Debug for GcHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("GcHandle").finish_non_exhaustive()
    }
}