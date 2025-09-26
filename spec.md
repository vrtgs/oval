# Primitive language reference

# Language goals

The language strives to be:
* static
* embeddable
* sandboxed
* garbage collected
* interpretable


# How to read token snippets
rust macros except `${token_type}` is turned into `$_:{token_type}`
and binary or (`|`) is read as "or"


# Types

## Primitives

### Integers
* `iN`: a signed twos complement integer with `N` bits 
* `uN`: an unsigned `N` bit integer
where `N` is 8, 16, 32, or 64.

### char type
represents a single character, more specifically a Unicode scalar value

### IEEE 754 floating point
there are 2 formats provided:
* `f32`: single precision floating point number
* `f64`: double precision floating point number

### slices 
a contiguous growable array type; written as `[$type]`

### strings
a UTF-8 encoded growable string; written as `str`

### references
* sync immutable (deeply immutable)
* mutable

## Structs
TODO

## Enums
TODO

# Functions
functions are just fancy constants that resolve to an expression of type `function`

functions are declared as follows:
```
fn $name:ident(
  $($($arg:ident : $arg_ty: type),+ $(,)?)?
) $(-> $ret: type)?
  $block_expr
```


# Expressions
* Literal: `$lit`
* Function Call: `$fn:expr ($($($arg:expr),+ $(,)?)?)` 
* Block: `{ $($stmnt)* }`
* Return Expression: `return $expr`

## Operators
lower precedence means the operator is evaluated first

Unary: precedence 1 (unary group)
* Dereference: `*$expr`
* Reference: `&$expr`
* Mutable Reference: `&mut $expr`
* Negation: `-$expr`

Binary Operator: precedence 2 (multiplication group)
* Multiplication: `$a:expr * $b: expr`
* Division: `$a:expr / $b: expr`
* Remainder: `$a:expr % $b: expr`
* Euclidean Modulo: `$a:expr %% $b: expr`
* Euclidean Division: `$a:expr /% $b: expr`

Binary Operator: precedence 3 (addition group)
* Addition: `$a:expr + $b: expr`
* Subtraction: `$a:expr - $b: expr`


# Statements
* Declaration: `let $(mut)? $pat;`
* Initialization/Mutation: `$pat = $expr;`
* Declaration + Initialization: `let $(mut)? $pat = $expr;`
* Dropped Expression: `$expr ;`
* Trailing Expression: `$expr`



# Errors
* 01: invalid token