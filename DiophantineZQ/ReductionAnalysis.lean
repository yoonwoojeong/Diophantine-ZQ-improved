/-
  DiophantineZQ.ReductionAnalysis
  ===============================
  Mathlib-backed formal verification of the Disjointness-in-D zero-test compression,
  positive-base power specialization, shared binomial numerator savings,
  and symbolic/concrete witness-cost reductions for Stages 1–3 on `diophantine-z-q`.
-/
import DiophantineZQ.Domains
import DiophantineZQ.SingleFold
import DiophantineZQ.SmallTM
import DiophantineZQ.Antihydra

namespace DiophantineZQ

/-! ## 1. Disjointness-in-`D` Zero-Test Compression -/

/-- Given slot capacity `K ≥ 1`, slot value `r ≤ K - 1`, and binary indicator `z ∈ {0, 1}`,
    `r + (K - 1) * z ≤ K - 1 ↔ (z = 1 → r = 0)`. -/
theorem disjoint_in_D_slot_zero_test (K r z : ℕ) (_hK : 1 ≤ K)
    (hr : r ≤ K - 1) (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (z = 1 → r = 0) := by
  rcases hz with rfl | rfl
  · simp [hr]
  · omega

/-- Without assuming `r ≤ K - 1` beforehand, the single condition `r + (K - 1) * z ≤ K - 1`
    (for `z ∈ {0, 1}`) is equivalent to both `r ≤ K - 1` and `(z = 1 → r = 0)`. -/
theorem combined_bound_and_zero_test_in_D (K r z : ℕ) (_hK : 1 ≤ K)
    (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (r ≤ K - 1 ∧ (z = 1 → r = 0)) := by
  rcases hz with rfl | rfl
  · simp
  · omega

/-! ## 2. Positive-Base Specialization of the `power` Template -/

/-- Whenever `1 ≤ Q`, the 3-way disjunction for `P = Q^E` over `ℕ` simplifies to the
    2-way disjunction `(E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q^E)`, eliminating the unreachable
    `Q = 0` branch and its witnesses. -/
theorem power_positive_base_iff (P Q E : ℕ) (hQ : 1 ≤ Q) :
    ((E = 0 ∧ P = 1) ∨ (Q = 0 ∧ 1 ≤ E ∧ P = 0) ∨ (1 ≤ Q ∧ 1 ≤ E ∧ P = Q ^ E)) ↔
    ((E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q ^ E)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h1 | _ | ⟨_, hE, hP⟩
    · exact Or.inl h1
    · omega
    · exact Or.inr ⟨hE, hP⟩
  · rcases h with h1 | ⟨hE, hP⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr ⟨hQ, hE, hP⟩)

/-! ## 3. Shared Binomial Numerator Savings -/

def unsharedMaskPowerCalls (M : ℕ) : ℕ := 3 * M
def sharedMaskPowerCalls (M : ℕ) : ℕ := 2 + M

/-- Sharing `(base_N, total_N)` across `M ≥ 1` `mask(A_m, N)` calls with common numerator `N`
    saves `2 * (M - 1)` `power` calls. -/
theorem shared_mask_power_savings (M : ℕ) (hM : 1 ≤ M) :
    unsharedMaskPowerCalls M - sharedMaskPowerCalls M = 2 * (M - 1) := by
  unfold unsharedMaskPowerCalls sharedMaskPowerCalls
  omega

theorem shared_mask_power_le (M : ℕ) (hM : 1 ≤ M) :
    sharedMaskPowerCalls M ≤ unsharedMaskPowerCalls M := by
  unfold unsharedMaskPowerCalls sharedMaskPowerCalls
  omega

/-! ## 4. Parametric Register-Machine Compiler Cost Model & Symbolic Reduction Theorems -/

structure RMCounts where
  numInputs : ℕ          -- 5 (`code_0..code_4`)
  numTupleWitnesses : ℕ  -- 4 (`tuple_0..tuple_3`)
  numRegisters : ℕ       -- 204
  numAddStates : ℕ       -- 376
  numSubStates : ℕ       -- 1022
  numHaltStates : ℕ      -- 1
  deriving Repr, DecidableEq

def glazerRM : RMCounts := {
  numInputs := 5
  numTupleWitnesses := 4
  numRegisters := 204
  numAddStates := 376
  numSubStates := 1022
  numHaltStates := 1
}

def RMCounts.numStates (c : RMCounts) : ℕ :=
  c.numAddStates + c.numSubStates + c.numHaltStates

theorem glazerRM_numStates : glazerRM.numStates = 1399 := rfl

/-- Parametric count of `power` bridges in the baseline compiler (`diophantine-z-q`):
    `2` global powers (`K = 2^c`, `T = B^q`) + `3` per state (`mask(S_i, F)`) +
    `3` per register (`mask(R_j, D)`) + `3 * 3` per subtract state (`bitAnd(Z_k, N_j, S_i)`) +
    `3` per register (`mask(N_j, D)`) + `3 * 2` per register (`orthogonal(2^c * V_j, R_j)` and `orthogonal(R_j, N_j)`). -/
def baselinePowerCalls (c : RMCounts) : ℕ :=
  2 + 3 * c.numStates + 3 * c.numRegisters + 9 * c.numSubStates + 9 * c.numRegisters

/-- Parametric count of `power` bridges in Stage 1 (Single-Fold Complement-Mask Zero-Tests):
    replaces `bitAnd(Z_k, N_j, S_i)` (`9 * numSubStates`) and the `N_j` register masks (`9 * numRegisters`)
    with one `mask(Z_k, F)` per subtract state (`3 * numSubStates`) and one complement-mask
    `mask(R_j, D - (2^c - 1)*Z_j)` per register (`3 * numRegisters`). -/
def stage1PowerCallsParam (c : RMCounts) : ℕ :=
  2 + 3 * c.numStates + 3 * c.numRegisters + 3 * c.numSubStates + 3 * c.numRegisters

/-- Parametric count of `power` bridges in Stages 2 & 3 (Shared Numerators `F, D` + Disjointness-in-`D`):
    `2` global powers (`K = 2^c`, `T = B^q`) + `(2 + numStates + numSubStates)` for `F` +
    `(2 + numRegisters)` for `D`. -/
def stage2PowerCallsParam (c : RMCounts) : ℕ :=
  2 + (2 + c.numStates + c.numSubStates) + (2 + c.numRegisters)

/-- Symbolic proof that for every register machine `c`, Stage 1 saves
    `6 * c.numSubStates + 6 * c.numRegisters` `power` bridges relative to Baseline. -/
theorem stage1_power_savings_symbolic (c : RMCounts) :
    baselinePowerCalls c - stage1PowerCallsParam c =
      6 * c.numSubStates + 6 * c.numRegisters := by
  unfold baselinePowerCalls stage1PowerCallsParam
  omega

/-- Symbolic proof that for every register machine with `1 ≤ numStates` and `2 ≤ numRegisters`,
    Stage 2 strictly reduces `power` calls relative to Stage 1. -/
theorem stage2_lt_stage1_power_symbolic (c : RMCounts)
    (hS : 1 ≤ c.numStates) (hR : 2 ≤ c.numRegisters) :
    stage2PowerCallsParam c < stage1PowerCallsParam c := by
  unfold stage2PowerCallsParam stage1PowerCallsParam
  omega

theorem glazer_baseline_powers_param_eq : baselinePowerCalls glazerRM = 15845 := by decide
theorem glazer_stage1_powers_param_eq : stage1PowerCallsParam glazerRM = 8489 := by decide
theorem glazer_stage2_powers_param_eq : stage2PowerCallsParam glazerRM = 2631 := by decide

/-! ## 5. Exact Kernel-Verified Witness Accounting for `diophantine-z-q` (Stages 1–3) -/

def slopeWitnesses : ℕ := 1298
def memberWitnesses : ℕ := 7
def heightCertWitnesses : ℕ := 3 * memberWitnesses + 9 + 9 + 21 + 27 * slopeWitnesses
def multiplyWitnesses : ℕ := 20 + 4 + 1 + 3 + heightCertWitnesses
def rawAddWitnesses : ℕ := 6
def naturalGuardWitnesses : ℕ := 20 + 20 + 15 + 4 * multiplyWitnesses + 2 * rawAddWitnesses + 1
def powerValueWitnesses : ℕ :=
  3 + 79 * 5 + 79 * naturalGuardWitnesses + 3 * 6 + 196 * (5 + rawAddWitnesses) + 190 * (5 + multiplyWitnesses)
def nonPrecisionRatWitnesses : ℕ :=
  5 + 7 + 406 + 5 + 35282 + 40 + 5 * 140654 + 53

theorem heightCertWitnesses_eq : heightCertWitnesses = 35106 := rfl
theorem multiplyWitnesses_eq : multiplyWitnesses = 35134 := rfl
theorem naturalGuardWitnesses_eq : naturalGuardWitnesses = 140604 := rfl
theorem powerValueWitnesses_eq : powerValueWitnesses = 17786698 := rfl
theorem nonPrecisionRatWitnesses_eq : nonPrecisionRatWitnesses = 739068 := rfl

def precisionRatWitnesses (explicitWitnesses numConstants numAdds numMuls numPowers perPowerWitnesses : ℕ) : ℕ :=
  3 + explicitWitnesses * 5
    + (5 + explicitWitnesses) * naturalGuardWitnesses
    + numConstants * 6
    + numAdds * (5 + rawAddWitnesses)
    + numMuls * (5 + multiplyWitnesses)
    + numPowers * (5 + perPowerWitnesses)

/-- Baseline (`diophantine-z-q`): `1,305,811` natural variables and `292,890,231,904` rational witnesses. -/
theorem glazer_precision_witnesses_eq :
    precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses = 292889492836 := rfl

theorem glazer_total_rat_witnesses_eq :
    nonPrecisionRatWitnesses + precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses
    = 292890231904 := rfl

theorem glazer_total_nat_vars_eq :
    5 + 54051 + 15845 * 79 = 1305811 := rfl

/-- Stage 1 (Single-Fold Complement-Mask Zero-Tests + Functional Elimination):
    `8,489` `power` calls, `700,367` natural variables, `157,081,401,474` rational witnesses. -/
def stage1NatVars : ℕ := 5 + 29731 + 8489 * 79
def stage1RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 29731 4 70565 54282 8489 powerValueWitnesses

theorem stage1_nat_vars_eq : stage1NatVars = 700367 := rfl
theorem stage1_rat_witnesses_eq : stage1RatWitnesses = 157081401474 := rfl
theorem stage1_rat_savings_eq :
    292890231904 - stage1RatWitnesses = 135808830430 := rfl

/-- Stage 2 (Shared Binomial Numerators `(F, D)` + Combined Disjointness-in-`D`):
    `2,631` `power` calls, `223,825` natural variables, `50,103,122,522` rational witnesses. -/
def stage2PowerCalls : ℕ := 2 + (2 + 2421) + (2 + 204)
def stage2ExplicitWitnesses : ℕ := 15971
def stage2NatVars : ℕ := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 79
def stage2RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls powerValueWitnesses

theorem stage2_power_calls_eq : stage2PowerCalls = 2631 := rfl
theorem stage2_nat_vars_eq : stage2NatVars = 223825 := rfl
theorem stage2_rat_witnesses_eq : stage2RatWitnesses = 50103122522 := rfl
theorem stage2_rat_savings_eq :
    292890231904 - stage2RatWitnesses = 242787109382 := rfl

/-- Stage 3 (Stage 2 + Positive-Base Specialization of `power_value` for `1 ≤ Q`):
    `2,631` `power` calls, `218,563` natural variables, `48,993,319,364` rational witnesses. -/
def positiveBasePowerValueWitnesses : ℕ :=
  3 + 77 * 5 + 77 * naturalGuardWitnesses + 3 * 6 + 192 * (5 + rawAddWitnesses) + 186 * (5 + multiplyWitnesses)

theorem positiveBasePowerValueWitnesses_eq : positiveBasePowerValueWitnesses = 17364880 := rfl

def stage3NatVars : ℕ := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 77
def stage3RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls positiveBasePowerValueWitnesses

theorem stage3_nat_vars_eq : stage3NatVars = 218563 := rfl
theorem stage3_rat_witnesses_eq : stage3RatWitnesses = 48993319364 := rfl
theorem stage3_rat_savings_eq :
    292890231904 - stage3RatWitnesses = 243896912540 := rfl

end DiophantineZQ
