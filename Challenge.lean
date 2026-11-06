/-
  Challenge.lean
  ==============
  Statements checked by `lake comparator` against `DiophantineZQ.lean`.
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

theorem packed_register_decode {B K q init : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t, t ≤ q → ρ t < K) (hα : ∀ t, t ≤ q → α t ≤ 1)
    (hγ : ∀ t, t ≤ q → γ t ≤ 1) (hinit : init < K)
    (heq : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t) + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t)
         = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
                + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t)) :
    ρ 0 = init ∧ (∀ t, t < q → ρ (t+1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by sorry

theorem complement_mask_iff_zero_test (c r z : ℕ)
    (hz : z = 0 ∨ z = 1) (hr : mask r (2 ^ c - 1)) :
    mask r ((2 ^ c - 1) * (1 - z)) ↔ (z = 1 → r = 0) := by sorry

theorem single_slot_branch_correct (c r r' s v z : ℕ)
    (hz : z = 0 ∨ z = 1) (hpart : s = v + z)
    (hr : mask r (2 ^ c - 1))
    (hguard : mask r ((2 ^ c - 1) * (1 - z)))
    (hstep : r' + v = r) :
    (s = 0 → v = 0 ∧ z = 0 ∧ r' = r) ∧
    (s = 1 ∧ r = 0 → v = 0 ∧ z = 1 ∧ r' = 0) ∧
    (s = 1 ∧ 0 < r → v = 1 ∧ z = 0 ∧ r' = r - 1) := by sorry

def baselinePowerCalls (states registers subs : ℕ) : ℕ :=
  2 + 3 * ((states + registers) + 3 * (registers + subs))

def stage1PowerCalls (states registers subs : ℕ) : ℕ :=
  2 + 3 * (states + registers + subs + registers)

theorem stage1_power_savings (states registers subs : ℕ) :
    baselinePowerCalls states registers subs - stage1PowerCalls states registers subs
      = 6 * registers + 6 * subs := by sorry

theorem glazer_baseline_power_calls : baselinePowerCalls 1399 204 1022 = 15845 := by sorry
theorem glazer_stage1_power_calls : stage1PowerCalls 1399 204 1022 = 8489 := by sorry

end DiophantineZQ
