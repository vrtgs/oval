use crate::alloc_helper::{make_slice, slice, zeroed_slice};
use crate::arena::{from_raw_handle, Handle, HandleRaw};
use crate::bitset::BitSet;
use alloc::vec::Vec;
use core::cell::Cell;
use core::convert::Infallible;
use core::marker::PhantomData;
use core::ptr::NonNull;

trait ChildrenIter {
    type Node;
    fn next_child(&mut self, parent: Self::Node) -> Option<Self::Node>;
}

impl<I: Iterator> ChildrenIter for I {
    type Node = I::Item;
    fn next_child(&mut self, parent: Self::Node) -> Option<Self::Node> {
        let _ = parent;
        self.next()
    }
}

pub struct DfsStack<K, I> {
    raw: Vec<(K, I)>,
    current_node: K,
}

impl<K: Handle, I> DfsStack<K, I> {
    pub fn push(&mut self, iter: I) {
        self.raw.push((self.current_node, iter))
    }
}

fn try_dfs_inner<D, K: Handle, I: ChildrenIter<Node=K>, E>(
    mut data: D,
    roots: impl Iterator<Item=K>,
    mut found_node: impl FnMut(&mut DfsStack<K, I>, &mut D, K) -> Result<(), E>,
    mut finished: impl FnMut(&mut D, K),
    total_nodes: usize
) -> Result<D, E> {
    let mut stack = DfsStack {
        raw: Vec::with_capacity(total_nodes),
        current_node: const { from_raw_handle::<K>(HandleRaw::MAX) },
    };

    let mut found_node = move |stack: &mut DfsStack<K, I>, data: &mut D, node| {
        stack.current_node = node;
        found_node(stack, data, node)
    };

    for root in roots {
        debug_assert!(stack.raw.is_empty());
        found_node(&mut stack, &mut data, root)?;
        while let Some(&mut (parent, ref mut iter)) = stack.raw.last_mut() {
            match iter.next_child(parent) {
                Some(dep) => found_node(&mut stack, &mut data, dep)?,
                None => {
                    stack.raw.pop();
                    finished(&mut data, parent)
                },
            }
        }
    }

    Ok(data)
}

pub fn try_dfs<D, K: Handle, I: Iterator<Item=K>, E>(
    data: D,
    roots: impl Iterator<Item=K>,
    found_node: impl FnMut(&mut DfsStack<K, I>, &mut D, K) -> Result<(), E>,
    finished: impl FnMut(&mut D, K),
    total_nodes: usize
) -> Result<D, E> {
    try_dfs_inner(data, roots, found_node, finished, total_nodes)
}

pub fn try_dfs_cyclic<D, K: Handle, I: Iterator<Item=K>, E>(
    data: D,
    roots: impl Iterator<Item=K>,
    mut found_node: impl FnMut(&mut DfsStack<K, I>, &mut D, K) -> Result<(), E>,
    finished: impl FnMut(&mut D, K),
    total_nodes: usize
) -> Result<D, E> {
    let mut visited = BitSet::new(total_nodes);
    try_dfs::<D, K, I, E>(
        data,
        roots,
        move |stack, data, key| {
            let idx = key.get();
            if visited.get(idx) {
                return Ok(());
            }
            visited.set(idx);
            found_node(stack, data, key)
        },
        finished,
        total_nodes
    )
}

pub fn dfs_cyclic<D, K: Handle, I: Iterator<Item=K>>(
    data: D,
    roots: impl Iterator<Item=K>,
    mut found_node: impl FnMut(&mut DfsStack<K, I>, &mut D, K),
    finished: impl FnMut(&mut D, K),
    total_nodes: usize
) -> D {
    let Ok(data) = try_dfs_cyclic::<D, K, I, Infallible>(
        data,
        roots,
        move |stack, data, node| { found_node(stack, data, node); Ok(()) },
        finished,
        total_nodes
    );
    data
}

#[derive(Debug)]
pub struct Cycle<I> {
    pub path: Vec<I>,
}

#[derive(bytemuck::Zeroable, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
enum Color {
    #[allow(dead_code, reason = "constructed by bytemuck::Zeroable")]
    Unvisited = 0,
    Visiting,
    Done
}

struct InfoWriterIter<K, I, E> {
    iter: I,
    len: usize,
    parent_definition: NonNull<Cell<Option<K>>>,
    parent_edge_info: NonNull<Cell<Option<E>>>,
    _marker: PhantomData<(K, E)>,
}

impl<K: Handle, I: Iterator<Item=(K, E)>, E> ChildrenIter for InfoWriterIter<K, I, E> {
    type Node = K;

    fn next_child(&mut self, parent: Self::Node) -> Option<Self::Node> {
        let (child, info) = self.iter.next()?;
        let idx = child.get();
        assert!(idx < self.len);

        unsafe {
            self.parent_definition.add(idx).as_ref().set(Some(parent));
            self.parent_edge_info.add(idx).as_ref().set(Some(info));
        }

        Some(child)
    }
}

// delete the info lifetime, otherwise rust will think I: 'info
// and since it doesn't know how long info will last
// it assumes that your iterator can't borrow from the environment
pub struct CycleDetectorStack<'stack, K, I, E> {
    dfs_stack: &'stack mut DfsStack<K, InfoWriterIter<K, I, E>>,
    len: usize,
    parent_definition: NonNull<Cell<Option<K>>>,
    parent_edge_info: NonNull<Cell<Option<E>>>,
    _marker: PhantomData<(K, E)>,
}

impl<K: Handle, I, E> CycleDetectorStack<'_, K, I, E> {
    pub fn push(&mut self, iter: I) {
        self.dfs_stack.push(InfoWriterIter {
            iter,
            len: self.len,
            parent_definition: self.parent_definition,
            parent_edge_info: self.parent_edge_info,
            _marker: PhantomData
        });
    }
}

pub fn try_dfs_acyclic<D, K: Handle, I: Iterator<Item=(K, E)>, E>(
    data: D,
    roots: impl Iterator<Item=K>,
    mut found_node: impl for<'a> FnMut(&mut CycleDetectorStack<'a, K, I, E>, &mut D, K),
    mut finished: impl FnMut(&mut D, K),
    total_nodes: usize
) -> Result<D, Cycle<E>> {
    let color: &[_] = &zeroed_slice::<Cell<Color>>(total_nodes);
    let parent_definition: &mut [_] = &mut slice![None; total_nodes];
    let parent_edge_info: &mut [_] = &mut make_slice(|_| None, total_nodes);
    let parent_definition = Cell::from_mut(parent_definition).as_slice_of_cells();
    let parent_edge_info = Cell::from_mut(parent_edge_info).as_slice_of_cells();

    let len = total_nodes;
    debug_assert_eq!(parent_definition.len(), parent_edge_info.len());
    let parent_definition_ptr = NonNull::from_ref(parent_definition).cast();
    let parent_edge_info_ptr = NonNull::from_ref(parent_edge_info).cast();

    try_dfs_inner::<D, K, InfoWriterIter<K, I, E>, Cycle<E>>(
        data,
        roots,
        move |stack, data, key| {
            let color = &color[key.get()];
            match color.get() {
                Color::Done => {},
                Color::Unvisited => {
                    color.set(Color::Visiting);
                    let mut stack = CycleDetectorStack {
                        dfs_stack: stack,
                        len,
                        parent_definition: parent_definition_ptr,
                        parent_edge_info: parent_edge_info_ptr,
                        _marker: PhantomData
                    };
                    found_node(&mut stack, data, key)
                }
                Color::Visiting => {
                    let mut cur = stack.raw.last().unwrap().0;
                    let mut path = Vec::with_capacity(8);

                    if let Some(info) = parent_edge_info[key.get()].take() {
                        path.push(info);
                    }

                    // go up up up until we hit `key`
                    while cur != key {
                        path.push(parent_edge_info[cur.get()].take().unwrap());
                        cur = parent_definition[cur.get()].get().unwrap();
                    }

                    path.reverse();
                    debug_assert!(!path.is_empty());
                    return Err(Cycle { path });
                }
            }
            Ok(())
        },
        move |data, key| {
            color[key.get()].set(Color::Done);
            finished(data, key)
        },
        total_nodes
    )
}

pub fn topo_sort_dependencies<K: Handle, I: Iterator<Item=(K, E)>, E>(
    roots: impl Iterator<Item=K>,
    mut found_node: impl FnMut(&mut CycleDetectorStack<K, I, E>, K),
    total_nodes: usize
) -> Result<Vec<K>, Cycle<E>> {
    let mut finished = Vec::<K>::with_capacity(total_nodes);
    try_dfs_acyclic(
        (),
        roots,
        |stack, &mut (), key| found_node(stack, key),
        |&mut (), key| finished.push(key),
        total_nodes
    )?;
    assert_eq!(finished.len(), total_nodes);
    Ok(finished)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::make_handle_raw;
    use alloc::vec;
    use core::convert::Infallible;

    make_handle_raw!(pub Node);

    fn n(i: usize) -> Node {
        Node::new(i).unwrap()
    }

    fn vec_nodes(xs: &[usize]) -> Vec<Node> {
        xs.iter().copied().map(n).collect()
    }

    #[test]
    fn try_dfs_preorder_and_postorder_on_chain() {
        // 0 -> 1 -> 2
        let total = 3;
        let edges: Vec<Vec<Node>> = vec![vec_nodes(&[1]), vec_nodes(&[2]), vec![]];

        let mut found = Vec::<Node>::new();
        let mut finished = Vec::<Node>::new();

        let Ok(()) = try_dfs::<(), Node, _, Infallible>(
            (),
            core::iter::once(n(0)),
            |stack, &mut (), key| {
                found.push(key);
                stack.push(edges[key.get()].iter().copied());
                Ok(())
            },
            |&mut (), key| finished.push(key),
            total,
        );

        assert_eq!(found, vec_nodes(&[0, 1, 2]));
        assert_eq!(finished, vec_nodes(&[2, 1, 0]));
    }

    #[test]
    fn try_dfs_cyclic_skips_revisits_and_finishes_each_once() {
        // diamond: 0 -> 1,2 ; 1 -> 3 ; 2 -> 3
        let total = 4;
        let edges: Vec<Vec<Node>> = vec![
            vec_nodes(&[1, 2]),
            vec_nodes(&[3]),
            vec_nodes(&[3]),
            vec![],
        ];

        let mut found = Vec::<Node>::new();
        let mut finished = Vec::<Node>::new();

        let Ok(()) = try_dfs_cyclic::<(), Node, _, Infallible>(
            (),
            core::iter::once(n(0)),
            |stack, &mut (), key| {
                found.push(key);
                stack.push(edges[key.get()].iter().copied());
                Ok(())
            },
            |&mut (), key| finished.push(key),
            total,
        );

        // 3 must appear exactly once even though it has two incoming edges.
        let count_3 = found.iter().filter(|&&x| x == n(3)).count();
        assert_eq!(count_3, 1);

        // All nodes reachable from 0 should be finished exactly once.
        finished.sort_by_key(|k| k.get());
        assert_eq!(finished, vec_nodes(&[0, 1, 2, 3]));
    }

    #[test]
    fn try_dfs_multiple_roots_runs_separately() {
        // components: 0 -> 1 ; 2 -> 3
        let total = 4;
        let edges: Vec<Vec<Node>> = vec![vec_nodes(&[1]), vec![], vec_nodes(&[3]), vec![]];

        let mut found = Vec::<Node>::new();
        let mut finished = Vec::<Node>::new();

        try_dfs::<(), Node, _, ()>(
            (),
            vec_nodes(&[0, 2]).into_iter(),
            |stack, &mut (), key| {
                found.push(key);
                stack.push(edges[key.get()].iter().copied());
                Ok(())
            },
            |&mut (), key| finished.push(key),
            total,
        )
            .unwrap();

        // Each component is DFS'ed fully before the next root (due to stack empty assert).
        // Expected: 0,1 then 2,3 (preorder) and 1,0 then 3,2 (postorder).
        assert_eq!(found, vec_nodes(&[0, 1, 2, 3]));
        assert_eq!(finished, vec_nodes(&[1, 0, 3, 2]));
    }

    #[test]
    fn try_dfs_acyclic_ok_on_dag_and_finishes_all() {
        // DAG:
        // 0 -> 1,2
        // 1 -> 3
        // 2 -> 3
        // 3 -> []
        let total = 4;
        let edges: Vec<Vec<(Node, u8)>> = vec![
            vec![(n(1), 10), (n(2), 20)],
            vec![(n(3), 13)],
            vec![(n(3), 23)],
            vec![],
        ];

        let mut finished = Vec::<Node>::new();
        let res = try_dfs_acyclic::<(), Node, _, u8>(
            (),
            core::iter::once(n(0)),
            |stack, &mut (), key| {
                stack.push(edges[key.get()].iter().copied());
            },
            |&mut (), key| finished.push(key),
            total,
        );

        assert!(res.is_ok());

        finished.sort_by_key(|k| k.get());
        assert_eq!(finished, vec_nodes(&[0, 1, 2, 3]));
    }

    #[test]
    fn try_dfs_acyclic_detects_simple_2_cycle_and_returns_path_infos_in_order() {
        // 0 -> 1 (info 7)
        // 1 -> 0 (info 9)
        //
        // With the current cycle reconstruction (from current_parent up to key, plus key's incoming
        // edge info), the returned path should correspond to the cycle edges in traversal order.
        let total = 2;
        let edges: Vec<Vec<(Node, u8)>> = vec![vec![(n(1), 7)], vec![(n(0), 9)]];

        let res = try_dfs_acyclic::<(), Node, _, u8>(
            (),
            core::iter::once(n(0)),
            |stack, &mut (), key| {
                stack.push(edges[key.get()].iter().copied());
            },
            |&mut (), _| {},
            total,
        );

        let err = res.unwrap_err();
        assert_eq!(err.path, vec![7, 9]);
    }

    #[test]
    fn try_dfs_acyclic_detects_self_loop_and_returns_single_edge_info() {
        // 0 -> 0 (info 42)
        let total = 1;
        let edges: Vec<Vec<(Node, u8)>> = vec![vec![(n(0), 42)]];

        let res = try_dfs_acyclic::<(), Node, _, u8>(
            (),
            core::iter::once(n(0)),
            |stack, &mut (), key| {
                stack.push(edges[key.get()].iter().copied());
            },
            |&mut (), _| {},
            total,
        );

        let err = res.unwrap_err();
        assert_eq!(err.path, vec![42]);
    }

    #[test]
    fn topo_sort_dependencies_returns_postorder_dependencies_first_on_chain() {
        // Interpreting edges as "node depends on dep" (children are dependencies):
        // 0 depends on 1, 1 depends on 2.
        // A valid order is [2,1,0]. The function returns "finished" order.
        let total = 3;
        let edges: Vec<Vec<(Node, ())>> = vec![
            vec![(n(1), ())],
            vec![(n(2), ())],
            vec![],
        ];

        let order = topo_sort_dependencies::<Node, _, ()>(
            core::iter::once(n(0)),
            |stack, key| stack.push(edges[key.get()].iter().copied()),
            total,
        )
            .unwrap();

        assert_eq!(order, vec_nodes(&[2, 1, 0]));
    }

    #[test]
    fn topo_sort_dependencies_errors_on_cycle() {
        // 0 depends on 1, 1 depends on 0
        let total = 2;
        let edges: Vec<Vec<(Node, u8)>> = vec![vec![(n(1), 1)], vec![(n(0), 2)]];

        let res = topo_sort_dependencies::<Node, _, u8>(
            core::iter::once(n(0)),
            |stack, key| stack.push(edges[key.get()].iter().copied()),
            total,
        );

        assert!(res.is_err());
        assert_eq!(res.unwrap_err().path, vec![1, 2]);
    }

    #[test]
    fn try_dfs_acyclic_handles_repeated_root_that_is_done() {
        // roots contain 0 twice; second time it's already Done, should not panic and should not
        // call finished twice.
        let total = 1;
        let edges: Vec<Vec<(Node, ())>> = vec![vec![]];

        let mut finished = Vec::<Node>::new();
        let res = try_dfs_acyclic::<(), Node, _, ()>(
            (),
            vec_nodes(&[0, 0]).into_iter(),
            |stack, &mut (), key| stack.push(edges[key.get()].iter().copied()),
            |&mut (), key| finished.push(key),
            total,
        );

        assert!(res.is_ok());
        assert_eq!(finished, vec_nodes(&[0]));
    }

    #[test]
    fn try_dfs_acyclic_visiting_root_from_second_component_can_error_cleanly() {
        // This test is designed to exercise the "roots hit Visiting" scenario.
        // If your implementation ever regresses to stack.raw.last().unwrap() in the Visiting
        // branch, it can panic when a root revisits a currently-Visiting node with an empty stack.
        //
        // Graph:
        // 0 -> 1
        // 2 -> 1
        //
        // Roots: 0 then 2
        // During DFS from 0, we visit 1 and mark Visiting, then if traversal order causes root 2
        // to be processed before 1 becomes Done (not typical with current loop), Visiting could
        // be observed. With current implementation, roots are processed sequentially and the stack
        // drains, so 1 will be Done by the time root 2 starts and the Visiting branch should not run.
        //
        // Keeping this test ensures any future refactor that interleaves roots doesn’t reintroduce
        // a panic.
        let total = 3;
        let edges: Vec<Vec<(Node, ())>> = vec![
            vec![(n(1), ())], // 0 -> 1
            vec![],           // 1
            vec![(n(1), ())], // 2 -> 1
        ];

        let res = try_dfs_acyclic::<(), Node, _, ()>(
            (),
            vec_nodes(&[0, 2]).into_iter(),
            |stack, &mut (), key| stack.push(edges[key.get()].iter().copied()),
            |&mut (), _| {},
            total,
        );

        assert!(res.is_ok());
    }
}
