## yaxpeax-lc87

[![crate](https://img.shields.io/crates/v/yaxpeax-lc87.svg?logo=rust)](https://crates.io/crates/yaxpeax-lc87)
[![documentation](https://docs.rs/yaxpeax-lc87/badge.svg)](https://docs.rs/yaxpeax-lc87)

an `lc87` decoder implemented as part of the yaxpeax proect, including traits provided by [`yaxpeax-arch`](https://git.iximeow.net/yaxpeax-arch/about/).

users of this library will either want to use [quick and dirty APIs](https://docs.rs/yaxpeax-lc87/latest/yaxpeax_lc87/index.html#usage), or more generic decode interfaces from `yaxpeax-arch` - appropriate when mixing `yaxpeax-lc87` with other `yaxpeax` decoders, such as `yaxpeax-x86`.

### features

* it exists
* pretty small?
* `#[no_std]`

### it exists

i'm aware of only one other `lc87` decoder on the internet: [chrisnoisel's Ghidra work](https://github.com/chrisnoisel/ghidra/tree/lc87).

### pretty small?

the `lc87` instruction set is very small. the decoder is about 300 lines of Rust. it seems plausible that there is more rodata in the form of opcode strings, than actual code to disassemble instructions.

### `#[no_std]`

if, for some reason, you want to disassemble `lc87` instructions without the Rust standard library around, that should work. this is primarily for consistency with other decoders than any need, and is not particularly tested.
