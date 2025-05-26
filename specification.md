# Primitive language reference

# Language goals

The language strives to be:
* static
* embeddable
* sandboxed
* garbage collected


# Types

## Primitives

All primitives copy

### Integers
* iN a signed twos compliment integer with N bits 
* uN an unsigned N bit integer
where N is one of { 8, 16, 32, 64 }

### char type
represents a single character, more specifically a Unicode scalar value

### IEEE 754 floating point
there are 2 formats provided:
* single precision floating point number `f32`
* double precision floating point number `f64`

### slices 
a contiguous growable array type written as `[$T: type]`

### strings
a UTF-8 encoded growable string

### references
* immutable (deeply immutable)
* mutable

## Structs
these are your typical aggregate types

```
struct $name:ident {
    $($identifier:ident : $ty:type)*
}
```

