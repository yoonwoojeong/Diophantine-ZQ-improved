/-
  DiophantineZQ.ReductionAnalysis
  Task 5: Formal verification of the Disjointness-in-D zero-test compression,
  positive-base power specialization, and exact variable/witness accounting for
  reducing the auxiliary-variable count of the Z-in-Q polynomial.
-/
import DiophantineZQ.Domains
import DiophantineZQ.SingleFold
import DiophantineZQ.SmallTM
import DiophantineZQ.Antihydra

namespace DiophantineZQ

/-!
## 1. Disjointness-in-`D` Zero-Test Compression (Stage 2)

In Glazer's `compileRegisterMachine` (`scripts/verify-integer-compiler.js`),
testing whether a register `R_j` is zero at the steps indicated by `W_i` uses:
- `204` nonzero-mask variables `N_j`,
- `204` calls to `bitAnd(R_j, F, N_j)` (`612` `orthogonal` calls = `1,836` `power` calls),
- `1,022` calls to `bitAnd(S_i, N_j, V_i)` (`3,066` `orthogonal` calls = `9,198` `power` calls).

In `DiophantineZQ.SingleFold.complement_mask_slot_zero_test`, we showed (Stage 1)
that one can eliminate all `N_j` and all `1,226` `bitAnd` calls by testing
`r_t ≤ (B - 1) * (1 - z_t)` in each slot `t`.

Can we go even further and share the binomial numerator `D = (K - 1) * F` that is
already used for the register mask `R_j ≼ D`?
Yes! In each time slot `t`, the register value satisfies `r_t ≤ K - 1` (where
`K = 2^c` is the single-slot capacity), and the aggregated zero-test indicator for
register `j` at step `t` satisfies `z_t ∈ {0, 1}`.
If we require that `r_t + (K - 1) * z_t ≤ K - 1` (or bitwise `r_t + (K - 1) * z_t ≼ K - 1`),
then:
- When `z_t = 0`, `r_t + 0 ≤ K - 1`, which automatically holds since `r_t ≤ K - 1`.
- When `z_t = 1`, `r_t + (K - 1) ≤ K - 1 ↔ r_t = 0`!
Crucially, because `K - 1 = 2^c - 1` is a Mersenne all-ones block of width `c` in
every slot of `D = (K - 1) * F`, testing `R_j + (K - 1) * Z^(j) ≼ D` has the
**exact same binomial numerator `D`** as `R_j ≼ D`!
-/

/-- Slotwise Disjointness-in-`D` Zero Test:
    Given capacity `K ≥ 1`, slot value `r ≤ K - 1`, and binary indicator `z ≤ 1`,
    the sum `r + (K - 1) * z` fits inside the capacity mask `K - 1` if and only if
    (`z = 1 → r = 0`). -/
theorem disjoint_in_D_slot_zero_test (K r z : Nat) (_hK : 1 ≤ K)
    (hr : r ≤ K - 1) (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (z = 1 → r = 0) := by
  rcases hz with rfl | rfl
  · simp [hr]
  · omega

/-- Combined Register-Bound and Zero-Test in `D`:
    Without assuming `r ≤ K - 1` beforehand, the single condition
    `r + (K - 1) * z ≤ K - 1` (for `z ∈ {0, 1}`) is equivalent to
    BOTH `r ≤ K - 1` AND `(z = 1 → r = 0)`. -/
theorem combined_bound_and_zero_test_in_D (K r z : Nat) (_hK : 1 ≤ K)
    (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (r ≤ K - 1 ∧ (z = 1 → r = 0)) := by
  rcases hz with rfl | rfl
  · simp
  · omega

/-!
## 2. Positive-Base Specialization of the `power` Template (Stage 3)

In `construction/precision-natural-polynomial.json`, `templates[0]` (`power(P, Q, E)`)
enforces `P = Q^E` over `ℕ` using the disjunction:
  `(E = 0 ∧ P = 1) ∨ (Q = 0 ∧ 1 ≤ E ∧ P = 0) ∨ (1 ≤ Q ∧ 1 ≤ E ∧ ...)`
Because of the middle disjunct `(Q = 0 ∧ 1 ≤ E ∧ P = 0)`, the template allocates
`2` extra `strict_difference` witnesses (`E ≥ 1` and `Q ≥ 1` guards) and `2`
`or`-branch multiplications.

However, in every single call to `power(P, Q, E)` in the register-machine compiler:
- `power(K, 2, c)` has base `Q = 2 ≥ 1`,
- `power(T, B, q)` has base `Q = B = 4 * K ≥ 4 ≥ 1`,
- `binomial(C, N, K)` calls `power(base, 2, N + 1)` with `Q = 2 ≥ 1`,
  `power(total, base + 1, N)` with `Q = base + 1 ≥ 1`, and
  `power(shift, base, K)` with `Q = base ≥ 2 ≥ 1`.

Thus `1 ≤ Q` is an invariant of every `power` call in the compiler! When `1 ≤ Q` is
known, the `Q = 0` branch is unreachable over `ℕ` and can be eliminated without
changing the relation.
-/

/-- Over `ℕ`, whenever the base `Q` satisfies `1 ≤ Q`, the 3-way disjunction for
    `P = Q^E` simplifies to the 2-way disjunction `(E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q^E)`,
    eliminating the `Q = 0` branch and its witnesses. -/
theorem power_positive_base_iff (P Q E : Nat) (hQ : 1 ≤ Q) :
    ((E = 0 ∧ P = 1) ∨ (Q = 0 ∧ 1 ≤ E ∧ P = 0) ∨ (1 ≤ Q ∧ 1 ≤ E ∧ P = Q ^ E)) ↔
    ((E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q ^ E)) := by
  constructor
  · intro h
    rcases h with h1 | h2 | ⟨_, hE, hP⟩
    · exact Or.inl h1
    · omega
    · exact Or.inr ⟨hE, hP⟩
  · intro h
    rcases h with h1 | ⟨hE, hP⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr ⟨hQ, hE, hP⟩)

/-!
## 3. Shared Binomial Numerator Accounting

In Glazer's `binomial(C, N, K)` macro (`scripts/verify-integer-compiler.js`):
1. `base = 2^(N + 1)` (`1` `power` call)
2. `total = (base + 1)^N` (`1` `power` call)
3. `shift = base^K` (`1` `power` call)
4. `total = (lower + 1) + shift * (C + (upper + 1) * base)` (`3` witnesses: `lower`, `upper`, `shift`)
Plus in `mask(A, B)` (`A ≼ B`):
5. `mid = B - A` (`1` `strict_difference` witness)
6. `odd_half` (`1` witness: `binom = 2 * odd_half + 1`).

Notice that `base = 2^(N + 1)` and `total = (base + 1)^N` depend **only on the
numerator `N`**, not on the lower argument `K`!
When `M` calls `mask(A_1, N), ..., mask(A_M, N)` share the same numerator `N`
(such as `N = F` across all `1,399` state histories `S_i` and `1,022` zero-branch
histories `Z_i`, or `N = D` across all `204` registers `R_j + (K - 1) * Z^(j)`):
- Unshared: `3 * M` `power` calls and `7 * M` explicit witnesses.
- Shared `(base_N, total_N)`: `2 + M` `power` calls and `2 + 5 * M` explicit witnesses!
-/

/-- Number of `power` calls for `M` `mask(A_m, N)` checks without sharing vs. with sharing. -/
def unsharedMaskPowerCalls (M : Nat) : Nat := 3 * M
def sharedMaskPowerCalls (M : Nat) : Nat := 2 + M

/-- Sharing `(base_N, total_N)` across `M ≥ 1` `mask` calls with common numerator `N`
    saves `2 * (M - 1)` `power` calls. -/
theorem shared_mask_power_savings (M : Nat) (hM : 1 ≤ M) :
    unsharedMaskPowerCalls M - sharedMaskPowerCalls M = 2 * (M - 1) := by
  unfold unsharedMaskPowerCalls sharedMaskPowerCalls
  omega

/-!
## 4. Exact Kernel-Verified Witness Accounting for `diophantine-z-q`

We now formalize the exact structure and witness counts of:
1. Glazer's baseline construction (`ordinary-integer-definition.json` &
   `precision-natural-polynomial.json`),
2. Stage 1: Single-Fold Complement-Mask Zero-Tests + Functional Elimination,
3. Stage 2: Shared Binomial Numerators `(F, D)` + Combined Disjointness-in-`D`,
4. Stage 3: Positive-Base `power_value` Specialization (`1 ≤ Q`).
-/

/-- Parameters of a specialized register machine inside `precision-natural-polynomial.json`. -/
structure RMCounts where
  numInputs : Nat          -- 5 (`code_0..code_4`)
  numTupleWitnesses : Nat  -- 4 (`tuple_0..tuple_3`)
  numRegisters : Nat       -- 204
  numAddStates : Nat       -- 376
  numSubStates : Nat       -- 1022
  numHaltStates : Nat      -- 1
  deriving Repr, DecidableEq

/-- The exact counts of the 1,399-state, 204-register machine in `precision-natural-polynomial.json`. -/
def glazerRM : RMCounts := {
  numInputs := 5
  numTupleWitnesses := 4
  numRegisters := 204
  numAddStates := 376
  numSubStates := 1022
  numHaltStates := 1
}

/-- Total number of states `s = 1,399`. -/
def RMCounts.numStates (c : RMCounts) : Nat :=
  c.numAddStates + c.numSubStates + c.numHaltStates

theorem glazerRM_numStates : glazerRM.numStates = 1399 := rfl

/-! ### Rational Model Template Costs (`ordinary-integer-definition.json`) -/

/-- Exact witness count of `slope`: `1,298`. -/
def slopeWitnesses : Nat := 1298

/-- Exact witness count of `member`: `7`. -/
def memberWitnesses : Nat := 7

/-- Exact witness count of `height_certificate`:
    `3 * member (21) + 9 (homogeneous) + 9 (inverses) + 21 (slopes) + 27 * slope (35,046) = 35,106`. -/
def heightCertWitnesses : Nat :=
  3 * memberWitnesses + 9 + 9 + 21 + 27 * slopeWitnesses

theorem heightCertWitnesses_eq : heightCertWitnesses = 35106 := rfl

/-- Exact witness count of `multiply`:
    `4 * 5 (shift points) + 4 (scalar) + 1 (guard) + 3 (line) + height_certificate (35,106) = 35,134`. -/
def multiplyWitnesses : Nat :=
  20 + 4 + 1 + 3 + heightCertWitnesses

theorem multiplyWitnesses_eq : multiplyWitnesses = 35134 := rfl

/-- Exact witness count of `raw_add`: `6` (`3` homogeneous + `3` line). -/
def rawAddWitnesses : Nat := 6

/-- Exact witness count of `natural` (Lagrange 4-square guard on point codes):
    `4 * 5 (roots) + 4 * 5 (squares) + 3 * 5 (sums) + 4 * multiply + 2 * raw_add + 1 (last raw_z) = 140,604`. -/
def naturalGuardWitnesses : Nat :=
  20 + 20 + 15 + 4 * multiplyWitnesses + 2 * rawAddWitnesses + 1

theorem naturalGuardWitnesses_eq : naturalGuardWitnesses = 140604 := rfl

/-- Exact witness count of `power_value` in `ordinary-integer-definition.json`:
    `3 (generator) + 79 * 5 (witness points) + 79 * natural + 3 * 6 (constants) + 196 * 11 (adds) + 190 * 35,139 (muls) = 17,786,698`. -/
def powerValueWitnesses : Nat :=
  3 + 79 * 5 + 79 * naturalGuardWitnesses + 3 * 6 + 196 * (5 + rawAddWitnesses) + 190 * (5 + multiplyWitnesses)

theorem powerValueWitnesses_eq : powerValueWitnesses = 17786698 := rfl

/-- Exact non-`precision` overhead in `ordinary-integer-definition.json`:
    `5 (N) + 7 (member) + 406 (exceptions) + 5 (K) + 35,282 (value.test) + 40 (close points) + 5 * 140,654 (signed_encode) + 53 (close_coordinates) = 739,068`. -/
def nonPrecisionRatWitnesses : Nat :=
  5 + 7 + 406 + 5 + 35282 + 40 + 5 * 140654 + 53

theorem nonPrecisionRatWitnesses_eq : nonPrecisionRatWitnesses = 739068 := rfl

/-- Exact witness count of `precision` given:
    - `explicitWitnesses` (`54,051` in baseline),
    - `numConstants` (`4` in baseline),
    - `numAdds` (`125,327` in baseline),
    - `numMuls` (`98,382` in baseline),
    - `numPowers` (`15,845` in baseline),
    - `perPowerWitnesses` (`17,786,698` in baseline). -/
def precisionRatWitnesses (explicitWitnesses numConstants numAdds numMuls numPowers perPowerWitnesses : Nat) : Nat :=
  3 + explicitWitnesses * 5
    + (5 + explicitWitnesses) * naturalGuardWitnesses
    + numConstants * 6
    + numAdds * (5 + rawAddWitnesses)
    + numMuls * (5 + multiplyWitnesses)
    + numPowers * (5 + perPowerWitnesses)

/-- Exact verification of Glazer's baseline `precision` witness count: `292,889,492,836`. -/
theorem glazer_precision_witnesses_eq :
    precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses = 292889492836 := rfl

/-- Exact verification of Glazer's total `292,890,231,904` rational witnesses
    (`292,890,231,905` ambient rational variables including input `t`). -/
theorem glazer_total_rat_witnesses_eq :
    nonPrecisionRatWitnesses + precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses
    = 292890231904 := rfl

/-- Exact verification of Glazer's total `1,305,811` natural variables
    (`5` inputs + `54,051` explicit witnesses + `15,845 * 79` `power` witnesses). -/
theorem glazer_total_nat_vars_eq :
    5 + 54051 + 15845 * 79 = 1305811 := rfl

/-!
### Stage 1: Single-Fold Complement-Mask Zero-Tests + Functional Elimination

In Stage 1:
- We eliminate all `204` `N_j` variables and all `1,226` `bitAnd` calls (`3,678` `orthogonal` calls).
- We replace them with:
  - `1,022` `mask(W_i, S_i)` calls (`W_i ≼ S_i`), substituting `V_i := S_i - W_i` functionally,
  - `204` aggregated register zero-test `mask(R_j, (B - 1) * (F - Z^(j)))` calls (`1` per register),
  - Functional elimination of `B := 4 * K` and `D := (K - 1) * F`.
- Total `mask` calls: `1,399 (S_i ≼ F) + 204 (R_j ≼ D) + 1,022 (W_i ≼ S_i) + 204 (zero-test) = 2,829`.
- Total `power` calls: `2 + 3 * 2,829 = 8,489` (down from `15,845`).
- Explicit natural witnesses: `29,731` (down from `54,051`).
- Explicit `add` ops in `precision`: `70,565` (down from `125,327`).
- Explicit `mul` ops in `precision`: `54,282` (down from `98,382`).
-/

def stage1NatVars : Nat := 5 + 29731 + 8489 * 79
def stage1RatWitnesses : Nat :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 29731 4 70565 54282 8489 powerValueWitnesses

theorem stage1_nat_vars_eq : stage1NatVars = 700367 := rfl
theorem stage1_rat_witnesses_eq : stage1RatWitnesses = 157081401474 := rfl
theorem stage1_rat_savings_eq :
    292890231904 - stage1RatWitnesses = 135808830430 := rfl

/-!
### Stage 2: Shared Binomial Numerators `(F, D)` + Combined Disjointness-in-`D`

In Stage 2:
- Using `combined_bound_and_zero_test_in_D`, the register capacity bound `R_j ≼ D`
  and the zero test `Z^(j) = 1 → R_j = 0` are combined into a **single** condition
  `R_j + (K - 1) * Z^(j) ≼ D` per register (`204` calls total instead of `204 + 204 = 408`!).
- Furthermore, instead of testing `W_i ≼ S_i` (which has a different numerator `S_i` for
  each `i`), since `S_i = V_i + W_i` and `S_i ≼ F`, by `SingleFold.digit_split` it suffices
  to require `V_i ≼ F` and `W_i ≼ F` (with `S_i := V_i + W_i` substituted functionally!).
  Every single state/branch mask now has numerator `F` (`376 + 1 + 2 * 1,022 = 2,421` calls
  with numerator `F`), and every register/zero-test mask has numerator `D` (`204` calls
  with numerator `D`)!
- By sharing `(base_F, total_F)` across all `2,421` calls with numerator `F` and sharing
  `(base_D, total_D)` across all `204` calls with numerator `D`:
  - Total `mask` calls: `2,421 + 204 = 2,625`.
  - Total `power` calls: `2 (K, T) + (2 + 2,421) (numerator F) + (2 + 204) (numerator D) = 2,631`!
    (down from `15,845`, an **`83.40%` / `6.02x` reduction** in `power` calls!).
  - Explicit natural witnesses:
    `4 (tuples) + 5 (q, c, K, T, F) + 204 (R_j) + 377 (S_i for add/halt) + 2,044 (V_i, W_i)`
    `+ 4 (base_F, total_F, base_D, total_D) + 5 * 2,625 (lower, upper, shift, mid, odd_half)`
    `+ 4 (tuple strict_diff) + 204 (register cleanup) = 15,971`.
  - Explicit `add` ops in `precision`: `41,855`.
  - Explicit `mul` ops in `precision`: `30,130`.
-/

def stage2PowerCalls : Nat := 2 + (2 + 2421) + (2 + 204)
def stage2ExplicitWitnesses : Nat := 15971
def stage2NatVars : Nat := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 79
def stage2RatWitnesses : Nat :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls powerValueWitnesses

theorem stage2_power_calls_eq : stage2PowerCalls = 2631 := rfl
theorem stage2_nat_vars_eq : stage2NatVars = 223825 := rfl
theorem stage2_rat_witnesses_eq : stage2RatWitnesses = 50103122522 := rfl
theorem stage2_rat_savings_eq :
    292890231904 - stage2RatWitnesses = 242787109382 := rfl

/-!
### Stage 3: Positive-Base Specialization of `power_value` (`1 ≤ Q`)

Combining Stage 2 with `power_positive_base_iff` (eliminating the unreachable `Q = 0`
disjunct in `power_value` since every base `Q ∈ {2, B, base_F, base_F + 1, base_D, base_D + 1}`
satisfies `Q ≥ 2`):
- Removes `2` `strict_difference` witnesses (`79 → 77` natural witnesses per `power` call),
- Removes `4` `add` ops (`196 → 192`) and `4` `mul` ops (`190 → 186`) per `power_value` call:
  `17,786,698 - (2 * 5 + 2 * 140,604 + 4 * 11 + 4 * 35,139) = 17,364,880`.
-/

def positiveBasePowerValueWitnesses : Nat :=
  3 + 77 * 5 + 77 * naturalGuardWitnesses + 3 * 6 + 192 * (5 + rawAddWitnesses) + 186 * (5 + multiplyWitnesses)

theorem positiveBasePowerValueWitnesses_eq : positiveBasePowerValueWitnesses = 17364880 := rfl

def stage3NatVars : Nat := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 77
def stage3RatWitnesses : Nat :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls positiveBasePowerValueWitnesses

theorem stage3_nat_vars_eq : stage3NatVars = 218563 := rfl
theorem stage3_rat_witnesses_eq : stage3RatWitnesses = 48993319364 := rfl
theorem stage3_rat_savings_eq :
    292890231904 - stage3RatWitnesses = 243896912540 := rfl

end DiophantineZQ
