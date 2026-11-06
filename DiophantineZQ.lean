/-
  DiophantineZQ.lean
  ==================
  Consolidated Mathlib formalization of the 5.98x witness reduction
  (292,890,231,904 -> 48,993,319,364 rational witnesses) for Elliot Glazer's
  explicit Diophantine definition of Z in Q (`elliotglazer/diophantine-z-q`).
-/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace DiophantineZQ

/-! ## 1. Bitwise-Binomial Macros via Lucas's Theorem (`Mathlib.Data.Nat.Choose.Lucas`) -/

/-- `Builder.odd(x)`: `x = 2 * half + 1`. -/
def odd_witness (x : ℕ) : Prop := ∃ half : ℕ, x = 2 * half + 1

/-- `Builder.mask(a, b)`: `Nat.choose b a` is odd. -/
def mask (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose b a ∧ odd_witness c

theorem odd_witness_iff_odd (x : ℕ) : odd_witness x ↔ Odd x := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

private theorem nat_eq_iff_halves (a b : ℕ) :
    a = b ↔ a % 2 = b % 2 ∧ a / 2 = b / 2 := by
  omega

private theorem and_eq_recur (a b : ℕ) :
    a &&& b = a ↔ a % 2 ≤ b % 2 ∧ (a / 2 &&& b / 2) = a / 2 := by
  rw [nat_eq_iff_halves (a &&& b) a, Nat.and_div_two]
  have h := Nat.and_mod_two_eq_one (a := a) (b := b)
  omega

private theorem choose_odd_recur (a b : ℕ) :
    Odd (Nat.choose b a) ↔ a % 2 ≤ b % 2 ∧ Odd (Nat.choose (b / 2) (a / 2)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := b) (k := a)
  change (Nat.choose b a) % 2 =
    (Nat.choose (b % 2) (a % 2) * Nat.choose (b / 2) (a / 2)) % 2 at h
  rw [Nat.odd_iff, h, ← Nat.odd_iff, Nat.odd_mul]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- By Lucas's theorem, `Nat.choose b a` is odd iff `a &&& b = a`. -/
theorem choose_odd_iff_land_eq (a b : ℕ) :
    Odd (Nat.choose b a) ↔ a &&& b = a := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a; simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [choose_odd_recur, and_eq_recur, ih (a / 2) hsmall]

theorem mask_iff_land_eq (a b : ℕ) :
    mask a b ↔ a &&& b = a := by
  simp only [mask, exists_eq_left, odd_witness_iff_odd, choose_odd_iff_land_eq]

private theorem pow2_pos (c : ℕ) : 0 < 2 ^ c := by
  induction c with
  | zero => decide
  | succ _ ih => rw [Nat.pow_succ]; omega

theorem land_two_pow_sub_one_eq_self_iff (c a : ℕ) :
    a &&& (2 ^ c - 1) = a ↔ a ≤ 2 ^ c - 1 := by
  have hpos := pow2_pos c
  rw [Nat.and_two_pow_sub_one_eq_mod a c]
  constructor
  · intro h
    have hlt : a % 2 ^ c < 2 ^ c := Nat.mod_lt a hpos
    omega
  · intro h
    exact Nat.mod_eq_of_lt (by omega)

/-! ## 2. Packed Base-`B` Register History Decoding (`Finset.sum`) -/

private theorem digit_split {M a b x y : ℕ} (ha : a < M) (hb : b < M)
    (h : a + x * M = b + y * M) : a = b ∧ x = y := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  have hmod : (a + x * M) % M = (b + y * M) % M := by rw [h]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  subst hmod
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hM (by omega)⟩

private theorem digits_eq_of_sum_eq {B : ℕ} (u v : ℕ → ℕ) (n : ℕ) :
    ∀ x y : ℕ, (∀ t, t < n → u t < B) → (∀ t, t < n → v t < B) →
      (∑ t ∈ Finset.range n, u t * B ^ t) + x * B ^ n
        = (∑ t ∈ Finset.range n, v t * B ^ t) + y * B ^ n →
      (∀ t, t < n → u t = v t) ∧ x = y := by
  induction n with
  | zero =>
    intro x y _ _ h
    simp only [Finset.sum_range_zero, pow_zero, mul_one, zero_add] at h
    exact ⟨fun t ht => absurd ht (Nat.not_lt_zero t), h⟩
  | succ n ih =>
    intro x y hu hv h
    have e1 : (∑ t ∈ Finset.range (n+1), u t * B ^ t) + x * B ^ (n+1)
        = (∑ t ∈ Finset.range n, u t * B ^ t) + (u n + x * B) * B ^ n := by
      rw [Finset.sum_range_succ]; ring
    have e2 : (∑ t ∈ Finset.range (n+1), v t * B ^ t) + y * B ^ (n+1)
        = (∑ t ∈ Finset.range n, v t * B ^ t) + (v n + y * B) * B ^ n := by
      rw [Finset.sum_range_succ]; ring
    obtain ⟨hlow, htop⟩ := ih (u n + x * B) (v n + y * B)
      (fun t ht => hu t (by omega)) (fun t ht => hv t (by omega))
      (e1.symm.trans (h.trans e2))
    obtain ⟨hn, hxy⟩ := digit_split (hu n (by omega)) (hv n (by omega)) htop
    refine ⟨fun t ht => ?_, hxy⟩
    by_cases htn : t < n
    · exact hlow t htn
    · have htn' : t = n := by omega
      rw [htn']; exact hn

/-- Carry-free decoding of the packed register equation `R + B*C = init + B*R + B*A`
    over `Finset.range (q + 1)`. -/
theorem packed_register_decode {B K q init : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t, t ≤ q → ρ t < K) (hα : ∀ t, t ≤ q → α t ≤ 1)
    (hγ : ∀ t, t ≤ q → γ t ≤ 1) (hinit : init < K)
    (heq : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t) + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t)
         = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
                + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t)) :
    ρ 0 = init ∧ (∀ t, t < q → ρ (t+1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by
  have hsplit : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
      = ρ 0 + (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t) * B := by
    rw [Finset.sum_range_succ', Finset.sum_mul, pow_zero, mul_one, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have h1 : ρ 0 + ((∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
        + (∑ t ∈ Finset.range (q+1), γ t * B ^ t)) * B
      = init + ((∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
        + (∑ t ∈ Finset.range (q+1), α t * B ^ t)) * B := by
    calc ρ 0 + ((∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
          + (∑ t ∈ Finset.range (q+1), γ t * B ^ t)) * B
        = (ρ 0 + (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t) * B)
          + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by ring
      _ = (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by rw [hsplit]
      _ = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t) := heq
      _ = init + ((∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + (∑ t ∈ Finset.range (q+1), α t * B ^ t)) * B := by ring
  obtain ⟨h0, h2⟩ := digit_split
    (Nat.lt_trans (hρ 0 (Nat.zero_le q)) hKB) (Nat.lt_trans hinit hKB) h1
  have e1 : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t) + γ q * B ^ q
      = (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
        + (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by
    have hd : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t)
        = (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
          + (∑ t ∈ Finset.range q, γ t * B ^ t) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hd, Finset.sum_range_succ]; ring
  have e2 : (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t) + (ρ q + α q) * B ^ q
      = (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
        + (∑ t ∈ Finset.range (q+1), α t * B ^ t) := by
    have hd : (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t)
        = (∑ t ∈ Finset.range q, ρ t * B ^ t)
          + (∑ t ∈ Finset.range q, α t * B ^ t) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hd, Finset.sum_range_succ, Finset.sum_range_succ]; ring
  obtain ⟨hstep, hlast⟩ := digits_eq_of_sum_eq (fun t => ρ (t+1) + γ t)
    (fun t => ρ t + α t) q (γ q) (ρ q + α q)
    (fun t ht => by have := hρ (t+1) (by omega); have := hγ t (by omega); omega)
    (fun t ht => by have := hρ t (by omega); have := hα t (by omega); omega)
    (e1.trans (h2.trans e2.symm))
  exact ⟨h0, hstep, hlast⟩

/-! ## 3. Core Compression Theorems (Stages 1–3) -/

/-- **Stage 1 (Single-Fold Complement-Mask Zero-Test):**
    For `z_t ∈ {0, 1}` and `mask r_t (2^c - 1)`,
    `mask r_t ((2^c - 1) * (1 - z_t)) ↔ (z_t = 1 → r_t = 0)`. -/
theorem complement_mask_iff_zero_test (c r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : mask r_t (2 ^ c - 1)) :
    mask r_t ((2 ^ c - 1) * (1 - z_t)) ↔ (z_t = 1 → r_t = 0) := by
  rw [mask_iff_land_eq] at hr_mask ⊢
  rcases hz with rfl | rfl
  · simp [hr_mask]
  · simp only [Nat.sub_self, Nat.mul_zero, Nat.and_zero, true_implies]
    exact ⟨Eq.symm, Eq.symm⟩

/-- **Stage 1 Branch Correctness:**
    Complement-mask zero testing plus the register recurrence `r_next + v_t = r_t`
    faithfully implements `sub` branching without `bitAnd` or `N_j` witnesses. -/
theorem single_fold_branch_correct (c r_t r_next s_t v_t z_t : ℕ)
    (_hs : s_t = 0 ∨ s_t = 1) (_hv : v_t = 0 ∨ v_t = 1) (hz : z_t = 0 ∨ z_t = 1)
    (hpart : s_t = v_t + z_t)
    (hr_mask : mask r_t (2 ^ c - 1))
    (hzero_guard : mask r_t ((2 ^ c - 1) * (1 - z_t)))
    (hstep : r_next + v_t = r_t) :
    (s_t = 0 → v_t = 0 ∧ z_t = 0 ∧ r_next = r_t) ∧
    (s_t = 1 ∧ r_t = 0 → v_t = 0 ∧ z_t = 1 ∧ r_next = 0) ∧
    (s_t = 1 ∧ 0 < r_t → v_t = 1 ∧ z_t = 0 ∧ r_next = r_t - 1) := by
  have hz_imp := (complement_mask_iff_zero_test c r_t z_t hz hr_mask).mp hzero_guard
  refine ⟨by intro; omega, by rintro ⟨_, _⟩; omega, ?_⟩
  rintro ⟨_, _⟩
  rcases hz with rfl | rfl
  · omega
  · have := hz_imp rfl; omega

/-- **Stage 2 (Combined Disjointness-in-`D` Binomial Mask):**
    A single binomial `mask (r + (2^c - 1) * z) (2^c - 1)` simultaneously enforces
    both the register capacity bound `mask r (2^c - 1)` and the zero test `z = 1 → r = 0`. -/
theorem disjoint_in_D_mask_iff (c r z : ℕ) (hz : z = 0 ∨ z = 1) :
    mask (r + (2 ^ c - 1) * z) (2 ^ c - 1) ↔
      (mask r (2 ^ c - 1) ∧ (z = 1 → r = 0)) := by
  rw [mask_iff_land_eq, mask_iff_land_eq,
      land_two_pow_sub_one_eq_self_iff, land_two_pow_sub_one_eq_self_iff]
  rcases hz with rfl | rfl
  · simp
  · omega

/-- **Stage 2 (Shared Binomial Numerators):**
    Sharing `(base_N, total_N)` across `M ≥ 1` `mask(A_m, N)` calls with common numerator `N`
    reduces `power` calls from `3 * M` to `2 + M`, saving `2 * (M - 1)` `power` calls. -/
def unsharedMaskPowerCalls (M : ℕ) : ℕ := 3 * M
def sharedMaskPowerCalls (M : ℕ) : ℕ := 2 + M

theorem shared_mask_power_savings (M : ℕ) (hM : 1 ≤ M) :
    unsharedMaskPowerCalls M - sharedMaskPowerCalls M = 2 * (M - 1) := by
  unfold unsharedMaskPowerCalls sharedMaskPowerCalls
  omega

/-- **Stage 3 (Positive-Base Specialization of `power_value`):**
    Whenever `1 ≤ Q`, the 3-way disjunction for `P = Q^E` over `ℕ` simplifies to the
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

/-! ## 4. Parametric & Concrete Witness Reductions for `diophantine-z-q` -/

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
      6 * c.numSubStates + 6 * c.numRegisters := by
  unfold baselinePowerCalls stage1PowerCallsParam
  omega

theorem stage2_lt_stage1_power_symbolic (c : RMCounts)
    (hS : 1 ≤ c.numStates) (hR : 2 ≤ c.numRegisters) :
    stage2PowerCallsParam c < stage1PowerCallsParam c := by
  unfold stage2PowerCallsParam stage1PowerCallsParam
  omega

theorem glazer_baseline_powers_eq : baselinePowerCalls glazerRM = 15845 := by decide
theorem glazer_stage1_powers_eq : stage1PowerCallsParam glazerRM = 8489 := by decide
theorem glazer_stage2_powers_eq : stage2PowerCallsParam glazerRM = 2631 := by decide

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

theorem baseline_nat_vars_eq : baselineNatVars = 1305811 := rfl
theorem baseline_rat_witnesses_eq : baselineRatWitnesses = 292890231904 := rfl

theorem stage1_nat_vars_eq : stage1NatVars = 700367 := rfl
theorem stage1_rat_witnesses_eq : stage1RatWitnesses = 157081401474 := rfl

theorem stage2_nat_vars_eq : stage2NatVars = 223825 := rfl
theorem stage2_rat_witnesses_eq : stage2RatWitnesses = 50103122522 := rfl

theorem stage3_nat_vars_eq : stage3NatVars = 218563 := rfl
theorem stage3_rat_witnesses_eq : stage3RatWitnesses = 48993319364 := rfl
theorem stage3_rat_savings_eq :
    baselineRatWitnesses - stage3RatWitnesses = 243896912540 := rfl

end DiophantineZQ
