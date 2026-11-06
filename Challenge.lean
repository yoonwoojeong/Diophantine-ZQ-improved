/-
  Challenge.lean
  ==============
  Self-contained specification module for `lake comparator` verification of
  `DiophantineZQ` against `Mathlib`.
-/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace DiophantineZQ

def odd_witness (x : ℕ) : Prop := ∃ half : ℕ, x = 2 * half + 1

def mask (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose b a ∧ odd_witness c

theorem choose_odd_iff_land_eq (a b : ℕ) :
    Odd (Nat.choose b a) ↔ a &&& b = a := by sorry

theorem mask_iff_land_eq (a b : ℕ) :
    mask a b ↔ a &&& b = a := by sorry

theorem land_two_pow_sub_one_eq_self_iff (c a : ℕ) :
    a &&& (2 ^ c - 1) = a ↔ a ≤ 2 ^ c - 1 := by sorry

theorem packed_register_decode {B K q init : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t, t ≤ q → ρ t < K) (hα : ∀ t, t ≤ q → α t ≤ 1)
    (hγ : ∀ t, t ≤ q → γ t ≤ 1) (hinit : init < K)
    (heq : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t) + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t)
         = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
                + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t)) :
    ρ 0 = init ∧ (∀ t, t < q → ρ (t+1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by sorry

theorem complement_mask_iff_zero_test (c r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : mask r_t (2 ^ c - 1)) :
    mask r_t ((2 ^ c - 1) * (1 - z_t)) ↔ (z_t = 1 → r_t = 0) := by sorry

theorem single_fold_branch_correct (c r_t r_next s_t v_t z_t : ℕ)
    (_hs : s_t = 0 ∨ s_t = 1) (_hv : v_t = 0 ∨ v_t = 1) (hz : z_t = 0 ∨ z_t = 1)
    (hpart : s_t = v_t + z_t)
    (hr_mask : mask r_t (2 ^ c - 1))
    (hzero_guard : mask r_t ((2 ^ c - 1) * (1 - z_t)))
    (hstep : r_next + v_t = r_t) :
    (s_t = 0 → v_t = 0 ∧ z_t = 0 ∧ r_next = r_t) ∧
    (s_t = 1 ∧ r_t = 0 → v_t = 0 ∧ z_t = 1 ∧ r_next = 0) ∧
    (s_t = 1 ∧ 0 < r_t → v_t = 1 ∧ z_t = 0 ∧ r_next = r_t - 1) := by sorry

theorem disjoint_in_D_mask_iff (c r z : ℕ) (hz : z = 0 ∨ z = 1) :
    mask (r + (2 ^ c - 1) * z) (2 ^ c - 1) ↔
      (mask r (2 ^ c - 1) ∧ (z = 1 → r = 0)) := by sorry

def unsharedMaskPowerCalls (M : ℕ) : ℕ := 3 * M
def sharedMaskPowerCalls (M : ℕ) : ℕ := 2 + M

theorem shared_mask_power_savings (M : ℕ) (hM : 1 ≤ M) :
    unsharedMaskPowerCalls M - sharedMaskPowerCalls M = 2 * (M - 1) := by sorry

theorem power_positive_base_iff (P Q E : ℕ) (hQ : 1 ≤ Q) :
    ((E = 0 ∧ P = 1) ∨ (Q = 0 ∧ 1 ≤ E ∧ P = 0) ∨ (1 ≤ Q ∧ 1 ≤ E ∧ P = Q ^ E)) ↔
    ((E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q ^ E)) := by sorry

structure RMCounts where
  numInputs : ℕ
  numTupleWitnesses : ℕ
  numRegisters : ℕ
  numAddStates : ℕ
  numSubStates : ℕ
  numHaltStates : ℕ
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

def baselinePowerCalls (c : RMCounts) : ℕ :=
  2 + 3 * c.numStates + 3 * c.numRegisters + 9 * c.numSubStates + 9 * c.numRegisters

def stage1PowerCallsParam (c : RMCounts) : ℕ :=
  2 + 3 * c.numStates + 3 * c.numRegisters + 3 * c.numSubStates + 3 * c.numRegisters

def stage2PowerCallsParam (c : RMCounts) : ℕ :=
  2 + (2 + c.numStates + c.numSubStates) + (2 + c.numRegisters)

theorem stage1_power_savings_symbolic (c : RMCounts) :
    baselinePowerCalls c - stage1PowerCallsParam c =
      6 * c.numSubStates + 6 * c.numRegisters := by sorry

theorem stage2_lt_stage1_power_symbolic (c : RMCounts)
    (hS : 1 ≤ c.numStates) (hR : 2 ≤ c.numRegisters) :
    stage2PowerCallsParam c < stage1PowerCallsParam c := by sorry

theorem glazer_baseline_powers_eq : baselinePowerCalls glazerRM = 15845 := by sorry
theorem glazer_stage1_powers_eq : stage1PowerCallsParam glazerRM = 8489 := by sorry
theorem glazer_stage2_powers_eq : stage2PowerCallsParam glazerRM = 2631 := by sorry

def slopeWitnesses : ℕ := 1298
def memberWitnesses : ℕ := 7
def heightCertWitnesses : ℕ := 3 * memberWitnesses + 9 + 9 + 21 + 27 * slopeWitnesses
def multiplyWitnesses : ℕ := 20 + 4 + 1 + 3 + heightCertWitnesses
def rawAddWitnesses : ℕ := 6
def naturalGuardWitnesses : ℕ := 20 + 20 + 15 + 4 * multiplyWitnesses + 2 * rawAddWitnesses + 1
def powerValueWitnesses : ℕ :=
  3 + 79 * 5 + 79 * naturalGuardWitnesses + 3 * 6 + 196 * (5 + rawAddWitnesses) + 190 * (5 + multiplyWitnesses)
def positiveBasePowerValueWitnesses : ℕ :=
  3 + 77 * 5 + 77 * naturalGuardWitnesses + 3 * 6 + 192 * (5 + rawAddWitnesses) + 186 * (5 + multiplyWitnesses)
def nonPrecisionRatWitnesses : ℕ :=
  5 + 7 + 406 + 5 + 35282 + 40 + 5 * 140654 + 53

def precisionRatWitnesses (explicitWitnesses numConstants numAdds numMuls numPowers perPowerWitnesses : ℕ) : ℕ :=
  3 + explicitWitnesses * 5
    + (5 + explicitWitnesses) * naturalGuardWitnesses
    + numConstants * 6
    + numAdds * (5 + rawAddWitnesses)
    + numMuls * (5 + multiplyWitnesses)
    + numPowers * (5 + perPowerWitnesses)

def baselineNatVars : ℕ := 5 + 54051 + 15845 * 79
def baselineRatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses

def stage1NatVars : ℕ := 5 + 29731 + 8489 * 79
def stage1RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 29731 4 70565 54282 8489 powerValueWitnesses

def stage2NatVars : ℕ := 5 + 15971 + 2631 * 79
def stage2RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 15971 4 41855 30130 2631 powerValueWitnesses

def stage3NatVars : ℕ := 5 + 15971 + 2631 * 77
def stage3RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 15971 4 41855 30130 2631 positiveBasePowerValueWitnesses

theorem baseline_nat_vars_eq : baselineNatVars = 1305811 := by sorry
theorem baseline_rat_witnesses_eq : baselineRatWitnesses = 292890231904 := by sorry

theorem stage1_nat_vars_eq : stage1NatVars = 700367 := by sorry
theorem stage1_rat_witnesses_eq : stage1RatWitnesses = 157081401474 := by sorry

theorem stage2_nat_vars_eq : stage2NatVars = 223825 := by sorry
theorem stage2_rat_witnesses_eq : stage2RatWitnesses = 50103122522 := by sorry

theorem stage3_nat_vars_eq : stage3NatVars = 218563 := by sorry
theorem stage3_rat_witnesses_eq : stage3RatWitnesses = 48993319364 := by sorry
theorem stage3_rat_savings_eq :
    baselineRatWitnesses - stage3RatWitnesses = 243896912540 := by sorry

end DiophantineZQ
