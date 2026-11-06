# Diophantine-ZQ-improved

**Mathlib & Comparator-Verified Single-Fold and Shared-Binomial Witness Compression, Busy Beaver / Cryptid Formalizations, and Structural Audit of the Explicit Diophantine Definition of $\mathbb{Z}$ in $\mathbb{Q}$**

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib4-v4.35.0-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![Comparator](https://img.shields.io/badge/lake_comparator-58_Theorems_Accepted-brightgreen)](#reproducible-verification)

---

## Executive Summary

In [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q), Elliot Glazer constructed an explicit polynomial $P_{\mathbb{Z}}(t, x_1, \dots, x_N) \in \mathbb{Z}[t, x_1, \dots, x_N]$ defining the integers inside the rationals:

$$t \in \mathbb{Z} \iff \exists x_1, \dots, x_N \in \mathbb{Q},\quad P_{\mathbb{Z}}(t, x_1, \dots, x_N) = 0$$

with **$N = 292,890,231,904$ rational witnesses** ($292,890,231,905$ ambient variables including $t$).

This repository provides a **rigorous `Mathlib`-backed Lean 4 formalization** (`v4.35.0`, `0` `sorry`s in `DiophantineZQ/`) verified end-to-end with **`lake comparator`** (`leanprover/comparator`) against a self-contained [`Challenge.lean`](Challenge.lean) specification (`58` theorems verified with standard axioms `["propext", "Quot.sound", "Classical.choice"]` in [`comparator/all.json`](comparator/all.json), plus `26` purely constructive theorems verified without `Classical.choice` in [`comparator/constructive.json`](comparator/constructive.json)):

1. **Mathlib Foundations (`DiophantineZQ/Domains.lean` & `DiophantineZQ/SingleFold.lean`):**
   - Formalizes single-fold Diophantine representations (`evalNat`, `SingleFoldRepresents`) over Mathlib's `MvPolynomial (Fin n ⊕ Fin m) ℤ` (matching `OAI.SingleFold.Represents` from [`openai/math`](https://github.com/openai/math)), rational polynomial formula compilation (`conjoin`, `disjoin`, `compile`), and denominator clearing (`commonDenominator`, `exists_integer_equation`) over `MvPolynomial (Fin n) ℚ` and `MvPolynomial (Fin n) ℤ`.
   - Formalizes the exact Kummer/Lucas bitwise-binomial macros (`odd_witness`, `mask a b := ∃ c, c = Nat.choose b a ∧ odd_witness c`, `orthogonal`, `bit_and`) using `Mathlib.Data.Nat.Choose.Lucas` (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`), and carry-free base-$B$ register-history decoding over `∑ t ∈ Finset.range (q+1), ρ t * B ^ t` (`packed_register_decode`, `signed_recurrence_iff`).
2. **A $5.98\times$ Genuine Witness Reduction on `diophantine-z-q` (`SingleFold.lean` & `ReductionAnalysis.lean`):**
   - By combining **Single-Fold Complement-Mask Zero-Tests** (`complement_mask_iff_zero_test`) with **Combined Disjointness-in-$D$ Zero-Testing** (`disjoint_in_D_mask_iff` proved directly on `mask` = `Odd (Nat.choose ...)`), **Shared Binomial Numerators $(F, D)$** (`shared_mask_power_savings`), and **Positive-Base `power_value` Specialization** (`power_positive_base_iff`), we reduce the number of `power` calls from **$15,845$ down to $2,631$ ($-83.40\%$)** and the total rational witness count from **$292,890,231,904$ down to $48,993,319,364$** (saving **$243,896,912,540$** genuine witnesses, **$-83.27\%$**) while lowering the syntactic degree bound from $2^{258}$ to $2^{254}$.
3. **Single-Fold Existence & Uniqueness for `BB2`, `clear`, and `BB(6)` Cryptid `Antihydra` (`SmallTM.lean` & `Antihydra.lean`):**
   - Proves both **witness existence and single-fold witness uniqueness** for the 2-state Busy Beaver champion `BB2` (`bb2StepPoly_iff_stepTM`, `bb2StepPoly_unique`, `bb2_halts`), the 1-`power` single-fold compression of Glazer's `clear` machine (`singleFoldClear_iff`, `singleFoldClear_unique`, $2,343 \to 85$ variables), and the 1-witness accelerated Collatz transition of the `BB(6)` Cryptid **Antihydra** (`antihydraStepPoly_iff_next`, `antihydraStepPoly_unique`, `antihydra_halts_iff_diophantine`) without assuming or attempting to resolve its open halting problem.

---

## Summary of Kernel & Comparator-Verified Witness Reductions (`ReductionAnalysis.lean`)

| Stage | Proven Compression Technique | `power` Calls | Total $\mathbb{N}$ Variables | Total $\mathbb{Q}$ Witnesses | Genuine $\mathbb{Q}$ Witnesses Saved | Reduction Factor | Syntactic Degree Bound |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :---: |
| **Baseline** | [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q) (100% of ambient vars referenced) | $15,845$ | $1,305,811$ | $292,890,231,904$ | $0$ (baseline) | $1.00\times$ | $\le 2^{258}$ |
| **Stage 1** | Single-Fold Complement-Mask Zero-Tests (`complement_mask_iff_zero_test`) | $8,489$ | $700,367$ | $157,081,401,474$ | $135,808,830,430$ ($-46.37\%$) | $1.86\times$ | $\le 2^{256}$ |
| **Stage 2** | Shared Binomial Numerators $(F, D)$ + Disjointness-in-$D$ (`disjoint_in_D_mask_iff`) | $2,631$ | $223,825$ | $50,103,122,522$ | $242,787,109,382$ ($-82.89\%$) | $5.85\times$ | $\le 2^{254}$ |
| **Stage 3** | Stage 2 + Positive-Base `power_value` Specialization (`power_positive_base_iff`) | $2,631$ | $218,563$ | **$48,993,319,364$** | **$243,896,912,540$ ($-83.27\%$)** | **$5.98\times$** | $\le 2^{254}$ |

---

## Core Mathematical Compressions (Verified with `Mathlib` & `lake comparator`)

### Stage 1: Single-Fold Complement-Mask Zero-Testing (`SingleFold.lean`)
In the baseline register-machine compiler, testing whether register $R_j$ is zero or nonzero across $1,022$ `sub` instructions uses $204$ nonzero-mask variables $N_j$ and $1,226$ `bitAnd` calls ($3,678$ `orthogonal` calls $= 11,034$ `power` calls).
- Using Lucas's theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat` $\implies$ `mask_iff_land_eq`), we prove in `complement_mask_iff_zero_test` that for $z_t \in \{0, 1\}$ and $\text{mask}(r_t, 2^w - 1)$,
  $$\text{mask}\bigl(r_t,\, (2^w - 1)(1 - z_t)\bigr) \iff (z_t = 1 \implies r_t = 0)$$
  while the register recurrence $r_{t+1} + v_t = r_t$ forces $r_t \ge 1$ whenever $v_t = 1$ (`single_fold_branch_correct`).
- Eliminating all $204$ `N_j` variables and all $1,226$ `bitAnd` calls saves $6 \cdot s_{\text{sub}} + 6 \cdot r$ `power` calls symbolically (`stage1_power_savings_symbolic`), cutting `power` calls on `glazerRM` from **$15,845 \to 8,489$** (`glazer_stage1_powers_param_eq`) and rational witnesses from **$292,890,231,904 \to 157,081,401,474$** (`stage1_rat_witnesses_eq`).

### Stage 2: Combined Disjointness-in-$D$ & Shared Binomial Numerators (`SingleFold.lean` & `ReductionAnalysis.lean`)
In [`DiophantineZQ/SingleFold.lean`](DiophantineZQ/SingleFold.lean) (`disjoint_in_D_mask_iff`), we prove directly on the binomial `mask` predicate (`Odd (Nat.choose ...)`) that for slot capacity $K = 2^c$ and $z_t \in \{0, 1\}$:

$$\text{mask}\bigl(r_t + (2^c - 1) z_t,\, 2^c - 1\bigr) \iff \Bigl(\text{mask}(r_t, 2^c - 1) \;\wedge\; (z_t = 1 \implies r_t = 0)\Bigr)$$

1. **Combined Register Bound & Zero-Test in $D$:** Because $D = (2^c - 1)F$ already has the Mersenne block $2^c - 1$ in every time slot $t$, the **single binomial mask**
   $$\text{mask}\bigl(R_j + (2^c - 1) Z^{(j)},\, D\bigr)$$
   simultaneously enforces both $\text{mask}(R_j, D)$ and the zero test ($z_t = 1 \implies r_t = 0$) in **one `mask(*, D)` call per register** ($204$ calls instead of $408$).
2. **Sharing Binomial Numerators $(F, D)$:** In Kummer's theorem (`binomial(C, N, K)`), $\text{base}_N = 2^{N + 1}$ and $\text{total}_N = (\text{base}_N + 1)^N$ depend **only on the numerator $N$**.
   - Splitting $S_i = V_i + W_i$ for `sub` states gives **$2,421$ masks sharing numerator $F$**.
   - Combining register bounds and zero tests gives **$204$ masks sharing numerator $D$**.
   - Sharing $(\text{base}_F, \text{total}_F)$ and $(\text{base}_D, \text{total}_D)$ cuts `power` calls from $3M$ to $2 + M$ (`shared_mask_power_savings`, `stage2_lt_stage1_power_symbolic`), reducing total `power` calls to **$2 + (2 + 2,421) + (2 + 204) = 2,631$** (`stage2_power_calls_eq`, **$-83.40\%$**) and rational witnesses to **$50,103,122,522$** (`stage2_rat_witnesses_eq`).

### Stage 3: Positive-Base Specialization of `power_value` (`ReductionAnalysis.lean`)
Every base $Q$ passed to `power(P, Q, E)` in the register-machine compiler belongs to $\{2, B, \text{base}_F, \text{base}_F + 1, \text{base}_D, \text{base}_D + 1\}$ and therefore satisfies $Q \ge 2$. Proving `power_positive_base_iff` eliminates the unreachable $(Q = 0 \wedge E \ge 1 \wedge P = 0)$ disjunct inside `power_value`, reducing each `power_value` call from $17,786,698 \to 17,364,880$ witnesses (`positiveBasePowerValueWitnesses_eq`) and bringing total rational witnesses down to **$48,993,319,364$** (`stage3_rat_witnesses_eq`).

---

## Repository Structure

```text
Diophantine-ZQ-improved/
├── Challenge.lean                       # Self-contained specification module (with `sorry`s) for `lake comparator`
├── DiophantineZQ.lean                   # Root solution module importing all 5 Mathlib-verified modules
├── DiophantineZQ/
│   ├── Domains.lean                     # MvPolynomial (Fin n ⊕ Fin m) ℤ/ℚ SingleFoldRepresents, EquationFormula,
│   │                                    # commonDenominator clearing, Z-vs-Q witness separation
│   ├── SingleFold.lean                  # Mathlib Lucas/Kummer bitwise macros (Nat.choose), Finset.sum packed
│   │                                    # register decoding, signed recurrence, disjoint_in_D_mask_iff
│   ├── SmallTM.lean                     # Base-2 half-tape Turing machines, BB(2) (1RB1LB_1LA1RH) existence &
│   │                                    # uniqueness, 1-power single-fold `clear` existence & uniqueness
│   ├── Antihydra.lean                   # BB(6) Cryptid Antihydra (1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA),
│   │                                    # 12-step startup, 1-witness Collatz existence, uniqueness & trajectory
│   └── ReductionAnalysis.lean           # Symbolic parametric RM compiler reduction theorems + exact Stages 1-3
│                                        # witness accounting for elliotglazer/diophantine-z-q
├── comparator/
│   ├── all.json                         # Comparator config for all 58 theorems (propext, Quot.sound, Classical.choice)
│   └── constructive.json                # Comparator config for 26 constructive theorems (propext, Quot.sound only)
├── docs/
│   └── TECHNICAL_REPORT.md              # Full technical report with audit tables, degree/coefficient tracking,
│                                        # and negative results (why naive Minsky compilation blows up 100x)
├── scripts/
│   └── audit_and_verify.py              # Standalone Python verifier & JSON artifact reachability/program-code auditor
├── .github/workflows/ci.yml             # GitHub Actions CI running lake build, lake comparator, and Python audit
├── lakefile.toml                        # Lean 4 Lake configuration (depends on mathlib v4.35.0)
├── lake-manifest.json                   # Pinned dependency manifest for mathlib v4.35.0
└── lean-toolchain                       # leanprover/lean4:v4.35.0
```

---

## Reproducible Verification

```bash
# 1. Fetch targeted Mathlib v4.35.0 .olean cache (takes ~30s)
lake exe cache get \
  Mathlib.Data.Nat.Choose.Lucas \
  Mathlib.Data.Nat.Bitwise \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Tactic.Ring \
  Mathlib.Algebra.Field.Rat \
  Mathlib.Algebra.MvPolynomial.Basic \
  Mathlib.Algebra.MvPolynomial.Rename \
  Mathlib.Algebra.Order.Ring.Rat \
  Mathlib.Data.Fin.Tuple.Basic \
  Mathlib.Data.Rat.Cast.Order \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Linarith

# 2. Build both the solution library (DiophantineZQ) and challenge spec (Challenge)
lake build DiophantineZQ Challenge

# 3. Verify with lake comparator that DiophantineZQ solves Challenge with only permitted axioms
lake comparator --config=comparator/all.json
lake comparator --config=comparator/constructive.json
# (In container/WSL environments without unprivileged userns, pass --inadvisably-no-sandbox)

# 4. Run the standalone Python witness accounting & JSON artifact verifier
python3 scripts/audit_and_verify.py
```

---

## License

Apache License 2.0 (see [LICENSE](LICENSE)).
