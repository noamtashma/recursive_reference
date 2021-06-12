# Recursive reference
This crate provides a way to walk on recursive structures easily and safely.
Rust's lifetime rules will usually force you to either only walk forward through the structure,
or use recursion, calling your method recursively every time you go down a node,
and returning every time you want to go back up, which leads to terrible code.

Instead, you can use the RecRef type, to safely and dynamically walk up
and down your recursive structure.

documentation: https://docs.rs/recursive_reference/

# License
dual licensed with MIT and APACHE 2.0
