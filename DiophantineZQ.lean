/-
  DiophantineZQ.lean
  ==================
  Machine-checked lemmas toward reducing the number of witnesses in Elliot Glazer's
  explicit Diophantine definition of ℤ in ℚ (`elliotglazer/diophantine-z-q`).

  Scope (see README): these are component lemmas only. No modified polynomial is
  constructed here, and no end-to-end witness reduction is claimed.
-/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DiophantineZQ

/-! ## 1. Glazer's `mask` macro is the bitwise submask relation (Lucas's theorem) -/

/-- `Builder.odd(x)`: `x = 2 * half + 1`. -/
def odd_witness (x : ℕ) : Prop := ∃ half : ℕ, x = 2 * half + 1

/-- `Builder.mask(a, b)`: `Nat.choose b a` is odd. -/
def mask (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose b a ∧ odd_witness c

theorem odd_witness_iff_odd (x : ℕ) : odd_witness x ↔ Odd x := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

private theorem and_eq_recur (a b : ℕ) :
    a &&& b = a ↔ a % 2 ≤ b % 2 ∧ (a / 2 &&& b / 2) = a / 2 := by
  have hh : ∀ x y : ℕ, x = y ↔ x % 2 = y % 2 ∧ x / 2 = y / 2 := fun x y => by omega
  rw [hh (a &&& b) a, Nat.and_div_two]
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

/-- Lucas's theorem at `p = 2`: `Nat.choose b a` is odd iff `a &&& b = a`. -/
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

/-! ## 2. Carry-free decoding of a packed base-`B` register history -/

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

/-- Glazer's register equation `R + B*C = init + B*R + B*A`, read in base `B` with
    digits bounded by `K < B`, yields the initial value, every transition, and the
    final-slot equation. -/
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

/-! ## 3. Single-digit complement-mask zero test (one time slot only)

  These are statements about a single base-`B` digit. Lifting them to Glazer's
  packed integers additionally needs: `B` is a power of two, every digit is `< B`,
  and the subtraction `D - (K-1)Z` does not borrow. That lifting is NOT proved here. -/

/-- For a digit `r ≤ 2^c - 1` and `z ∈ {0, 1}`:
    `r ≼ (2^c - 1)(1 - z) ↔ (z = 1 → r = 0)`. -/
theorem complement_mask_iff_zero_test (c r z : ℕ)
    (hz : z = 0 ∨ z = 1) (hr : mask r (2 ^ c - 1)) :
    mask r ((2 ^ c - 1) * (1 - z)) ↔ (z = 1 → r = 0) := by
  rw [mask_iff_land_eq] at hr ⊢
  rcases hz with rfl | rfl
  · simp [hr]
  · simp only [Nat.sub_self, Nat.mul_zero, Nat.and_zero, true_implies]
    exact ⟨Eq.symm, Eq.symm⟩

/-- At one slot: given the complement-mask zero test and the decoded recurrence
    `r' + v = r`, the branch digits `v, z` are forced to the correct `sub` branch. -/
theorem single_slot_branch_correct (c r r' s v z : ℕ)
    (hz : z = 0 ∨ z = 1) (hpart : s = v + z)
    (hr : mask r (2 ^ c - 1))
    (hguard : mask r ((2 ^ c - 1) * (1 - z)))
    (hstep : r' + v = r) :
    (s = 0 → v = 0 ∧ z = 0 ∧ r' = r) ∧
    (s = 1 ∧ r = 0 → v = 0 ∧ z = 1 ∧ r' = 0) ∧
    (s = 1 ∧ 0 < r → v = 1 ∧ z = 0 ∧ r' = r - 1) := by
  have himp := (complement_mask_iff_zero_test c r z hz hr).mp hguard
  refine ⟨by intro; omega, by rintro ⟨_, _⟩; omega, ?_⟩
  rintro ⟨_, _⟩
  rcases hz with rfl | rfl
  · omega
  · have := himp rfl; omega

/-! ## 4. `power`-call counts (structural formulas)

  Baseline: `2 + 3 * (#masks + 3 * #bitAnd)` with masks `s_i ≼ F` (one per state) and
  `r_j ≼ D` (one per register), and `bitAnd` calls for `N_j` (one per register) and
  sub branching (one per sub state). This matches `integer-diophantine-compiler.js`.

  Stage 1 (proposal): drop `N_j` and both `bitAnd` families; add `V_i ≼ s_i` (one per
  sub state) and `r_j ≼ D - (K-1)Z⁽ʲ⁾` (one per register). Only the call count is
  stated; correctness of the modified compiler is not proved here. -/

def baselinePowerCalls (states registers subs : ℕ) : ℕ :=
  2 + 3 * ((states + registers) + 3 * (registers + subs))

def stage1PowerCalls (states registers subs : ℕ) : ℕ :=
  2 + 3 * (states + registers + subs + registers)

theorem stage1_power_savings (states registers subs : ℕ) :
    baselinePowerCalls states registers subs - stage1PowerCalls states registers subs
      = 6 * registers + 6 * subs := by
  unfold baselinePowerCalls stage1PowerCalls
  omega

/-- Glazer's universal machine: 1,399 states, 204 registers, 1,022 sub states. -/
theorem glazer_baseline_power_calls : baselinePowerCalls 1399 204 1022 = 15845 := by decide
theorem glazer_stage1_power_calls : stage1PowerCalls 1399 204 1022 = 8489 := by decide

end DiophantineZQ
