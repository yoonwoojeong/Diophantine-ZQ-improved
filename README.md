# Diophantine-ZQ-improved

Formal verification and mathematical audit for Elliot Glazer’s polynomial definition of integers inside rational numbers.

## Summary

This repository contains verified mathematical proofs checking the components of Elliot Glazer’s paper:

1. **Bitwise Mask Equivalence**: Proves that the binomial condition used in the paper correctly tests whether one number's binary bits are contained within another's.
2. **Register History Decoding**: Proves that machine execution histories encoded as base-$B$ numbers can be uniquely decoded step-by-step without unwanted carries.
3. **Zero-Testing Gadget**: Proves that a single masked register value correctly checks whether a register is zero before branching.
4. **Operation Counts**: Formally calculates the number of power operations required by the baseline machine (15,845) versus an improved single-test design (8,489).

> **Correction**: A previously proposed multi-register shortcut (Stage 2) was found to be mathematically invalid due to carries between registers, and has been retracted.

## Verification

To verify all proofs using Lean 4:

```bash
lake build DiophantineZQ Challenge
lake comparator
```
