# Diophantine-ZQ-improved

Formal verification in Lean 4 (`Mathlib` + `lake comparator`) of a **$5.98\times$ witness reduction** for Elliot Glazer's explicit Diophantine definition of $\mathbb{Z}$ in $\mathbb{Q}$ ([`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q)), reducing the number of rational witnesses from **$292,890,231,904$** down to **$48,993,319,364$** ($-83.27\%$).

## Result

| Stage | Compression | `power` Calls | Total $\mathbb{N}$ Variables | Total $\mathbb{Q}$ Witnesses | Reduction |
| :--- | :--- | ---: | ---: | ---: | ---: |
| **Baseline** | [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q) | $15,845$ | $1,305,811$ | $292,890,231,904$ | $1.00\times$ |
| **Stage 1** | Single-Fold Complement-Mask Zero-Tests (`complement_mask_iff_zero_test`) | $8,489$ | $700,367$ | $157,081,401,474$ | $1.86\times$ |
| **Stage 2** | Shared Binomial Numerators $(F, D)$ + Disjointness-in-$D$ (`disjoint_in_D_mask_iff`) | $2,631$ | $223,825$ | $50,103,122,522$ | $5.85\times$ |
| **Stage 3** | Positive-Base `power_value` Specialization (`power_positive_base_iff`) | $2,631$ | $218,563$ | **$48,993,319,364$** | **$5.98\times$** |

## Files

- [`DiophantineZQ.lean`](DiophantineZQ.lean) — Consolidated `Mathlib` proof of all theorems (`0` `sorry`s).
- [`Challenge.lean`](Challenge.lean) — Self-contained challenge specification for `lake comparator`.
- [`comparator.json`](comparator.json) — Configuration for `lake comparator`.

## Verification

```bash
lake exe cache get Mathlib.Data.Nat.Choose.Lucas Mathlib.Data.Nat.Bitwise Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
lake build DiophantineZQ Challenge
lake comparator
```
