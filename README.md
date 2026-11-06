# Diophantine-ZQ-improved

Component lemmas and structural analysis for Elliot Glazer's explicit Diophantine definition of $\mathbb{Z}$ in $\mathbb{Q}$ ([`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q)).

## Scope and Status

- **Lucas characterization of `mask`**: Formally verified in Lean 4 via `Mathlib.Data.Nat.Choose.Lucas`. Glazer's `mask(a, b)` predicate (`Nat.choose b a` is odd) is equivalent to the bitwise submask relation $a \mathbin{\&} b = a$.
- **Carry-free register decoding**: Formally verified in Lean 4, formalizing carry-free base-$B$ history decoding for $R + B \cdot C = \text{init} + B \cdot R + B \cdot A$ when digits are bounded below $K < B$.
- **Single-slot complement-mask zero test**: Formally verified for a single slot: for $r \le 2^c - 1$ and $z \in \{0, 1\}$, $r \mathbin{\&} ((2^c - 1)(1 - z)) = r \iff (z = 1 \implies r = 0)$.
- **Stage 1 power-call count (proposal)**: Replaces `bitAnd` zero-testing with a complement-mask test, structurally reducing `power` template calls from $15,845$ to $8,489$. End-to-end multi-slot packed equivalence and rational witness count remain unverified proposals.
- **Stage 2/3 and 5.98× claim**: Retracted. The combined Disjointness-in-$D$ gadget fails across packed words due to inter-slot borrowing (counterexample: $K=2, B=8, D=9, Z=1, R=7$).

## Formal Verification

The component theorems in `DiophantineZQ.lean` are verified against `Challenge.lean` using `lake comparator`:

```bash
lake exe cache get Mathlib.Data.Nat.Choose.Lucas Mathlib.Data.Nat.Bitwise Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring
lake build DiophantineZQ Challenge
lake comparator
```

## Files

- [`DiophantineZQ.lean`](DiophantineZQ.lean): Lean 4 proofs of component lemmas and structural call formulas.
- [`Challenge.lean`](Challenge.lean): Specification interface checked by `lake comparator`.
- [`comparator.json`](comparator.json): Comparator theorem list and permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).
