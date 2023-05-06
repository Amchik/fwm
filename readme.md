# FWM Virtual machine

FWM is a shitty virtual machine that crashes if you try to sum two numbers.
Written using `c2rust` utility so just ignore over 4000 lines of output on `cargo clippy`.

## Concepts

1. Be shitty
2. Be shitty
3. Be shitty

It doesn't supports many things because it made just for fun. I got F for
my project but made this!

## Hello world

FWM assembler (`fwm-as` crate and `fwmc` binary) support strings but `fwm` not, so...

```
xor %r0, %r0

# write "hello world" to stack
mov [%r0; 0], 104 # h
mov [%r0; 1], 101 # e
mov [%r0; 2], 108 # l
mov [%r0; 3], 108 # l
mov [%r0; 4], 111 # o
mov [%r0; 5], 32  # space
mov [%r0; 6], 119 # w
mov [%r0; 7], 111 # o
mov [%r0; 8], 114 # r
mov [%r0; 9], 108 # l
mov [%r0; 10], 100 # d

# write the string to stdout
write 0, 11 # write 11 bytes from string that starts in 0th stack byte to stdout
```

By the way, it faster than python! (idk how)

## to-do...

Do `cargo b -r` and run `target/release/rustc`. Also try `cargo doc --open` and read
about `fwm_base`...

