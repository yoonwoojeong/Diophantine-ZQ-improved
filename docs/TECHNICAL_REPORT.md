# Technical Report: Single-Fold and Shared-Binomial Witness Compression for $\mathbb{Z}$-in-$\mathbb{Q}$

## 1. Overview & Problem Statement

In [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q), Elliot Glazer constructed an explicit polynomial $P_{\mathbb{Z}}(t, x_1, \dots, x_N) \in \mathbb{Z}[t, x_1, \dots, x_N]$ defining the integers inside the rationals:

$$t \in \mathbb{Z} \iff \exists x_1, \dots, x_N \in \mathbb{Q},\; P_{\mathbb{Z}}(t, x_1, \dots, x_N) = 0$$

where the released artifact `ordinary-integer-definition.json` has **$N = 292,890,231,904$ rational witnesses** ($292,890,231,905$ total variables including the parameter $t$).

This report documents:
1. **Task 1 (Exact Structural Audit):** Distinguishing ambient, actively referenced, and functionally eliminable variables across both the natural layer (`precision-natural-polynomial.json`) and the elliptic-curve point-code layer (`ordinary-integer-definition.json`), and decoding the $3,181,317$-digit program constant $e$ at node `0`.
2. **Task 2 (Small Turing Machine Formalization):** Formalizing binary Turing machines via base-2 half-tape stacks in Lean 4 (`DiophantineZQ/SmallTM.lean`), proving the 6-step halting and 4-witness single-step Diophantine representation of `BB2` (`1RB1LB_1LA1RH`), and proving a single-fold compression of Glazer's `clear` machine from $29$ `power` calls ($2,343$ variables) to $1$ `power` call ($85$ variables).
3. **Task 3 (Single-Fold Computation-History Compression):** Formalizing unique dyadic base selection, carry-free base-$B$ digit splitting, signed counter recurrences without terminal cleanup, and complement-mask zero testing (`DiophantineZQ/SingleFold.lean`).
4. **Task 4 (`BB(6)` Cryptid Antihydra Formalization):** Formalizing the 6-state Cryptid **Antihydra** (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) and its accelerated 3-counter Collatz-like map from [`google-deepmind/cryptids`](https://github.com/google-deepmind/cryptids), proving its 1-witness single-step and full-trajectory Diophantine equivalences (`DiophantineZQ/Antihydra.lean`) without assuming or attempting to resolve its open halting status.
5. **Task 5 (Established Variable Reductions vs. Failed Approaches):** Proving an exact **$5.98\times$ reduction** ($292,890,231,904 \to 48,993,319,364$ rational witnesses) across Stages 1–3 (`DiophantineZQ/ReductionAnalysis.lean`), tracking degree and coefficient bounds, and documenting why naive direct compilation of the decoded $146,780$-state Minsky machine fails ($100\times$ blowup).

---

## 2. Exact Audit of `elliotglazer/diophantine-z-q`

### 2.1 Complete Breakdown of the $1,305,811$ Natural Variables (`precision-natural-polynomial.json`)

Every variable in `precision-natural-polynomial.json` was audited for DAG reachability from the root node (`293619`). **All $54,056$ explicit variables and all $15,845$ `power` template calls ($1,251,755$ private witnesses) are actively referenced ($0$ dead natural variables):**

| Category | Variable / Macro Role | Count | Subtotal ($\mathbb{N}$ vars) | Active in Root DAG? |
| :--- | :--- | ---: | ---: | :---: |
| **Parameters** | `code_0 .. code_4` | $5$ | $5$ | 100% ($5 / 5$) |
| **Cantor Wrapper** | `tuple_0 .. tuple_3` + $4$ `strict_difference` guards | $4 + 4$ | $8$ | 100% ($8 / 8$) |
| **Global Packing** | `time` ($q$), `digit_bits` ($c$), `digit_capacity` ($K$), `history_base` ($B$), `last_place` ($T$), `time_mask` ($F$), `register_mask` ($D$) | $7$ | $7$ | 100% ($7 / 7$) |
| **Histories** | Register histories $R_0 \dots R_{203}$ ($204$) + State histories $S_0 \dots S_{1398}$ ($1,399$) | $204 + 1,399$ | $1,603$ | 100% ($1,603 / 1,603$) |
| **Zero-Test Masks** | Nonzero register masks $N_0 \dots N_{203}$ | $204$ | $204$ | 100% ($204 / 204$) |
| **Branch Histories** | `sub_nonzero` $V_i$ ($1,022$) + `sub_zero` $W_i$ ($1,022$) | $2 \times 1,022$ | $2,044$ | 100% ($2,044 / 2,044$) |
| **`bitAnd` Calls** | $204$ `bitAnd(R_j, F, N_j)` + $1,022$ `bitAnd(S_i, N_j, V_i)` ($2$ remainder vars each) | $1,226 \times 2$ | $2,452$ | 100% ($2,452 / 2,452$) |
| **`orthogonal` Calls** | $3 \times 1,226 = 3,678$ calls (`orthogonal_binomial`) | $3,678 \times 1$ | $3,678$ | 100% ($3,678 / 3,678$) |
| **`mask` Calls** | $1,399$ `mask(S_i, F)` + $204$ `mask(R_j, D)` (`mask_binomial`) | $1,603 \times 1$ | $1,603$ | 100% ($1,603 / 1,603$) |
| **`binomial` Calls** | $3,678$ (from `orthogonal`) + $1,603$ (from `mask`) $= 5,281$ calls $\times 5$ vars (`base`, `total`, `shift`, `lower`, `upper`) | $5,281 \times 5$ | $26,405$ | 100% ($26,405 / 26,405$) |
| **`odd_half` Vars** | Parity witness `binom = 2 * odd_half + 1` for each of the $5,281$ `binomial` calls | $5,281 \times 1$ | $5,281$ | 100% ($5,281 / 5,281$) |
| **`strict_difference`** | $204$ (register cleanup) $+ 1,603$ (`mask` mid) $+ 5,281$ (`binomial` $K \le N$) $+ 3,678$ (`orthogonal` guard) | $10,766$ | $10,766$ | 100% ($10,766 / 10,766$) |
| **Explicit Subtotal** | **All explicit $\mathbb{N}$ variables in `precision-natural-polynomial.json`** | | **$54,056$** | **100% ($54,056 / 54,056$)** |
| **`power` Template** | $2$ (`K = 2^c`, `T = B^q`) $+ 3 \times 5,281$ (`binomial`) $= 15,845$ calls $\times 79$ private witnesses | $15,845 \times 79$ | $1,251,755$ | 100% ($1,251,755 / 1,251,755$) |
| **Grand Total ($\mathbb{N}$)** | **$5$ inputs $+ 54,051$ explicit witnesses $+ 1,251,755$ `power` witnesses** (`glazer_total_nat_vars_eq`) | | **$1,305,811$** | **100% ($1,305,811 / 1,305,811$)** |

---

### 2.2 Complete Breakdown of the $292,890,231,905$ Rational Variables (`ordinary-integer-definition.json`)

In `ordinary-integer-definition.json`, the root recipe `integers` has $1$ rational parameter $t$ and **$292,890,231,904$ rational witnesses** (kernel-verified in `DiophantineZQ.glazer_total_rat_witnesses_eq`):

| Recipe / Template Component | Witness Breakdown Formula | Exact $\mathbb{Q}$ Witnesses | Share of Total |
| :--- | :--- | ---: | ---: |
| **Parameter $t$** | Input to $P_{\mathbb{Z}}(t, \vec{x}) = 0$ | ($1$ parameter) | — |
| **Outer Point & Membership** | Point code $N$ ($5$) + `member(N)` ($7$) | $12$ | $< 0.0001\%$ |
| **Exception & Test Guards** | `value.exceptions` ($406$) + point $\mathcal{K}$ ($5$) + `value.test` ($35,282$) | $35,693$ | $0.00001\%$ |
| **Close-Coordinate Bridge** | $8$ point codes ($40$) + $5 \times \text{value.signed\_encode}$ ($5 \times 140,654$) + `value.close_coordinates` ($53$) | $703,363$ | $0.00024\%$ |
| **Non-`precision` Subtotal** | `nonPrecisionRatWitnesses` | **$739,068$** | **$0.00025\%$** |
| **`precision`: Generator & Constants** | Generator $(g_0, g_1, g_2)$ ($3$) + $4$ constants ($4 \times 6 = 24$) | $27$ | $< 0.0001\%$ |
| **`precision`: Explicit Source Points** | $54,051 \times 5$ point-code coordinates | $270,255$ | $0.00009\%$ |
| **`precision`: Explicit `natural` Guards** | $54,056 \times 140,604$ (4-square point-code guards) | $7,600,489,824$ | $2.59500\%$ |
| **`precision`: Explicit `add` Ops** | $125,327 \times (5 + 6)$ (`point` + `raw_add`) | $1,378,597$ | $0.00047\%$ |
| **`precision`: Explicit `mul` Ops** | $98,382 \times (5 + 35,134)$ (`point` + `multiply`) | $3,457,045,098$ | $1.18032\%$ |
| **`precision`: `power_value` Calls** | $15,845 \times (5 + 17,786,698)$ (`point` + `power_value`) | $281,830,309,035$ | **$96.22387\%$** |
| **`precision` Subtotal** | `glazer_precision_witnesses_eq` | **$292,889,492,836$** | **$99.99975\%$** |
| **Grand Total ($\mathbb{Q}$ Witnesses)** | `glazer_total_rat_witnesses_eq` | **$292,890,231,904$** | **$100.00000\%$** |

#### Formal Parameters vs. Active Existential Witnesses
Bottom-up active-parameter propagation across all $23$ library templates and $7$ recipes shows:
- **Existential witnesses:** $292,890,231,904 / 292,890,231,904$ ($100\%$) are referenced in the expanded root polynomial.
- **Formal template parameters:** In template `[10] multiply.guard` ($15$ parameters: `t`, `A_x..A_v`, `B_x..B_v`, `C_x..C_v`; $1$ witness: `guard_inverse`), $12$ parameters are unreferenced in the expression DAG, and the remaining $3$ vanish from the final polynomial node (`1 * guard_inverse - 1 = 0`) because at finite-box bound $T = 0$, the product over false triples in $[0,0]^3$ has $0$ factors. Because `multiply` also passes `A, B, C` into `multiply.scalar` and `height_certificate`, all $15$ coordinates remain actively constrained in `multiply`. We do **not** count unreferenced formal parameters as variable savings.

---

## 3. Established Variable Reductions on `diophantine-z-q` (Stages 1–3)

All counts below are kernel-verified in [`DiophantineZQ/ReductionAnalysis.lean`](../DiophantineZQ/ReductionAnalysis.lean):

| Stage | `power` Calls | Explicit $\mathbb{N}$ Vars | Total $\mathbb{N}$ Vars | Total $\mathbb{Q}$ Witnesses | Genuine $\mathbb{Q}$ Witnesses Saved | Reduction Factor |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **Baseline (`diophantine-z-q`)** | $15,845$ | $54,056$ | $1,305,811$ | $292,890,231,904$ | $0$ (baseline) | $1.00\times$ |
| **Stage 1: Single-Fold Complement-Mask Zero-Tests** | $8,489$ | $29,736$ | $700,367$ | $157,081,401,474$ | $135,808,830,430$ ($-46.37\%$) | $1.86\times$ |
| **Stage 2: Shared Binomial $(F, D)$ + Disjointness-in-$D$** | $2,631$ | $15,976$ | $223,825$ | $50,103,122,522$ | $242,787,109,382$ ($-82.89\%$) | $5.85\times$ |
| **Stage 3: Stage 2 + Positive-Base `power_value` ($Q \ge 2$)** | $2,631$ | $15,976$ | $218,563$ | **$48,993,319,364$** | **$243,896,912,540$ ($-83.27\%$)** | **$5.98\times$** |

### Tracking Degree and Coefficient Bounds Across Stages 1–3

In `BoundedIntegerPolynomial.lean`, Glazer bounds the syntactic degree and $\ell_1$ coefficient norm of the root polynomial via its binary expression-DAG height $h$ (`rootSyntaxHeight = 258`) and maximum leaf constant $C_{\max}$ (`node 0`, $e \approx 10^{3,181,316}$):

| Metric | Baseline (`diophantine-z-q`) | Stage 1 (Single-Fold Zero-Test) | Stage 2 (Shared $(F, D)$ + Disjoint-$D$) | Stage 3 (Positive-Base `power`) |
| :--- | :--- | :--- | :--- | :--- |
| **Max Leaf Constant $C_{\max}$** | $e \approx 10^{3,181,316}$ | Unchanged | Unchanged | Unchanged |
| **Balanced Sum Tree Depth** | $\lceil \log_2(293,619) \rceil = 19$ | $\lceil \log_2(161,000) \rceil = 18$ | $\lceil \log_2(52,000) \rceil = 16$ | $\lceil \log_2(50,000) \rceil = 16$ |
| **Root Syntax Height $h$** | $258$ | $256$ ($-2$) | $254$ ($-4$) | $254$ ($-4$) |
| **Syntactic Degree Bound $2^h$** | $\le 2^{258}$ | $\le 2^{256}$ (**$4\times$ lower**) | $\le 2^{254}$ (**$16\times$ lower**) | $\le 2^{254}$ (**$16\times$ lower**) |
| **Individual Constraint Degree** | $\le 12$ in point coords | Unchanged ($\le 12$) | Unchanged ($\le 12$) | Unchanged ($\le 12$) |

Because the linear combinations $Z^{(j)} = \sum_{i \text{ tests } j} W_i$ and $(K - 1)Z^{(j)}$ are represented by explicit intermediate `add` and `mul` point-code witnesses in `precision` (already counted in the `41,855` `add` and `30,130` `mul` operations of Stages 2–3), **no individual polynomial constraint increases in degree**, while balanced sum-of-squares tree depth decreases by $4$ levels.

---

## 4. Established Results vs. Failed Approaches & Open Directions

### 4.1 Established Results (Verified with `Mathlib` & `lake comparator`)
All **58 theorems** in `DiophantineZQ` are checked against `Challenge.lean` via `lake comparator --config=comparator/all.json` (and **26 purely constructive theorems** without `Classical.choice` via `comparator/constructive.json`):
1. **Multivariate Polynomials, Rational Compilation, Denominator Clearing & Functional Elimination (`DiophantineZQ/Domains.lean`):**
   - `SingleFoldRepresents.toDiophantine`, `eval_conjoin_eq_zero_iff`, `eval_disjoin_eq_zero_iff`, `eval_compile_eq_zero_iff`, `exists_conjunction_fresh_iff`, `exists_disjunction_fresh_iff`, `commonDenominator_pos`, `exists_integer_multiple`, `exists_integer_equation`, `int_vs_rat_witness_separation`, `eval_hasUnreferencedTail_indep`, `functional_witness_elimination_int`, `functional_sub_elimination_nat`.
2. **Kummer/Lucas Bitwise-Binomial Macros, Packed Histories, and Zero-Test Compressions (`DiophantineZQ/SingleFold.lean` & `ReductionAnalysis.lean`):**
   - `choose_odd_iff_land_eq` (via `Choose.choose_modEq_choose_mod_mul_choose_div_nat`), `choose_add_odd_iff_land_eq_zero`, `mask_iff_land_eq`, `orthogonal_iff_land_eq_zero`, `bit_and_iff_land_eq`, `dyadic_exponent_unique`, `dyadic_exponent_exists`, `packHistory_eq_finset_sum`, `packed_register_decode`, `packHistory_eq_iff`, `signed_recurrence_iff`, `complement_mask_slot_zero_test`, `complement_mask_iff_zero_test`, `single_fold_branch_correct`, `disjoint_in_D_mask_iff`, `disjoint_in_D_slot_zero_test`, `combined_bound_and_zero_test_in_D`, `power_positive_base_iff`, `shared_mask_power_savings`.
3. **Small TM (`BB2`, `clear`) & `BB(6)` Cryptid (`Antihydra`) Existence and Single-Fold Uniqueness (`DiophantineZQ/SmallTM.lean` & `Antihydra.lean`):**
   - `bb2StepPoly_iff_stepTM`, `bb2StepPoly_unique`, `bb2_halts_in_6`, `bb2_halts`, `singleFoldClear_iff` ($2,343 \to 85$ variables), `singleFoldClear_unique`, `antihydra_reaches_start_in_12_steps`, `antihydraStepPoly_iff_next`, `antihydraStepPoly_unique`, `antihydra_halts_iff_diophantine`.
4. **Symbolic Parametric & Exact Stage 1–3 Witness Reductions ($292,890,231,904 \to 48,993,319,364$):**
   - `stage1_power_savings_symbolic`, `stage2_lt_stage1_power_symbolic`, `glazer_baseline_powers_param_eq`, `glazer_stage1_powers_param_eq`, `glazer_stage2_powers_param_eq`, `glazer_total_rat_witnesses_eq`, `glazer_total_nat_vars_eq`, `stage1_rat_witnesses_eq`, `stage2_rat_witnesses_eq`, `stage3_rat_witnesses_eq`, `stage3_rat_savings_eq`.

### 4.2 Failed Approaches (Tested and Rejected)
1. **Searching for Unreferenced Existential Witnesses in the Released JSON Artifacts:**
   - *Result (Failed):* Complete DAG reachability proved that $100\%$ of the $1,305,811$ natural variables and $100\%$ of the $292,890,231,904$ rational witnesses are referenced in the root polynomial.
2. **Naive Direct Compilation of the Decoded $146,780$-State Precision Machine:**
   - *Result (Failed):* Decoding the $3,181,317$-digit constant $e$ at node `0` of `precision-natural-polynomial.json` revealed a $146,780$-state, $23,633$-register Minsky machine ($39,077$ `add`, $107,702$ `sub`, $1$ `halt`). Compiling that unary Minsky machine directly without universal interpretation requires $1,693,262$ `power` calls and $\approx 3.01 \times 10^{13}$ rational witnesses—over **$100\times$ larger** than the universal-interpreter baseline!
3. **Eliminating `W_i` Functionally via $W_i := S_i - V_i$ Over $\mathbb{Z}$ Without a Non-Negativity Guard:**
   - *Result (Failed without `V_i ≼ S_i`):* Removing `W_i` removes its explicit `natural` (4-square) guard, which is unsound over $\mathbb{Z}$ unless the remaining constraints already force $S_i - V_i \ge 0$. In Stage 2, we instead keep $V_i \ge 0$ and $W_i \ge 0$ (`V_i ≼ F` and `W_i ≼ F`) and eliminate $S_i := V_i + W_i$ functionally, which automatically preserves $S_i \ge 0$ and aligns all $2,421$ state/branch masks to share the single numerator $F$.
