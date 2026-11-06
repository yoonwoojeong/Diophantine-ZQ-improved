# Diophantine-ZQ-improved

Formally verified component lemmas for Elliot Glazer's explicit Diophantine definition of $\mathbb{Z}$ in $\mathbb{Q}$ ([`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q)).

## Verified Results

All theorems in [`DiophantineZQ.lean`](DiophantineZQ.lean) are machine-checked in Lean 4 against `Mathlib` and verified with `lake comparator`:

1. **Lucas Equivalence (`choose_odd_iff_land_eq`)**:
   $$a \mathbin{\&} b = a \iff \binom{b}{a} \equiv 1 \pmod 2$$
   Establishes that Glazer's `mask(a, b)` predicate directly corresponds to the bitwise submask relation.

2. **Carry-Free Packed Register Decoding (`packed_register_decode`)**:
   Proves uniqueness and transition correctness of packed register histories under base-$B$ encoding when digits are strictly bounded below $K < B$.

3. **Complement-Mask Zero Test (`complement_mask_iff_zero_test`)**:
   Proves for a single digit $r \le 2^c - 1$ and indicator $z \in \{0, 1\}$:
   $$r \mathbin{\&} ((2^c - 1)(1 - z)) = r \iff (z = 1 \implies r = 0)$$

4. **Single-Slot Branch Deduction (`single_slot_branch_correct`)**:
   Deduces transition actions from the partition $s = v + z$ and the complement mask.

5. **Structural Power Call Counts (`glazer_baseline_power_calls`, `glazer_stage1_power_calls`)**:
   Exact evaluation of register machine power invocations ($15,845$ baseline vs $8,489$ single-fold).

> **Note on Stage 2 / 5.98× claim**: Retracted. Dropping explicit register bounds in packed words allows inter-slot borrowing (counterexample: $K=2, B=8, D=9, Z=1, R=7$).

## Build & Verify

```bash
lake build DiophantineZQ Challenge
lake comparator
```

## Structure

- [`DiophantineZQ.lean`](DiophantineZQ.lean): Lean 4 proofs.
- [`Challenge.lean`](Challenge.lean): Target specification.
- [`comparator.json`](comparator.json): Verified declaration list and permitted axioms.
