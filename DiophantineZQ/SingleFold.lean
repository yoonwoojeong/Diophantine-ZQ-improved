/-
  DiophantineZQ.SingleFold
  ========================
  Mathlib-backed formalization of Kummer/Lucas bitwise-binomial macros,
  large-base Finset computation-history packing, and single-fold witness compression:
  1. Exact Kummer/Lucas bitwise macros (`odd_witness`, `mask`, `orthogonal`, `bit_and`)
     using `Nat.choose` and `Mathlib.Data.Nat.Choose.Lucas`.
  2. Unique dyadic base selection (`dyadic_exponent_unique`, `dyadic_exponent_exists`).
  3. Carry-free base-`B` computation history decoding via `Finset.sum`
     (`packed_register_decode`, `signed_recurrence_iff`, `packHistory_eq_finset_sum`).
  4. Single-fold complement-mask zero testing (`complement_mask_slot_zero_test`,
     `complement_mask_iff_zero_test`, `single_fold_branch_correct`) and combined
     Disjointness-in-`D` mask equivalence (`disjoint_in_D_mask_iff`).
-/

import DiophantineZQ.Domains
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DiophantineZQ

/-! ## 1. Kummer/Lucas Bitwise-Binomial Macros (`Nat.choose` & `Mathlib.Data.Nat.Choose.Lucas`) -/

/-- `Builder.odd(x)`: a fresh natural witness `half` satisfies `x = 2 * half + 1`. -/
def odd_witness (x : ℕ) : Prop := ∃ half : ℕ, x = 2 * half + 1

/-- `Builder.mask(a, b)`: its binomial witness `c = b.choose a` is odd. -/
def mask (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose b a ∧ odd_witness c

/-- `Builder.orthogonal(a, b)`: its binomial witness `c = (a + b).choose a` is odd. -/
def orthogonal (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose (a + b) a ∧ odd_witness c

/-- `Builder.bitAnd(z, x, y)` with two fresh natural remainder witnesses `a, b`. -/
def bit_and (z x y : ℕ) : Prop :=
  ∃ a b : ℕ,
    x = z + a ∧ y = z + b ∧
    orthogonal z a ∧ orthogonal z b ∧ orthogonal a b

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

private theorem and_zero_recur (a b : ℕ) :
    a &&& b = 0 ↔ (a % 2 = 0 ∨ b % 2 = 0) ∧ (a / 2 &&& b / 2) = 0 := by
  rw [nat_eq_iff_halves (a &&& b) 0, Nat.and_div_two]
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

/-- By Lucas's theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`),
    `Nat.choose b a` is odd if and only if `a` is a bitwise submask of `b` (`a &&& b = a`). -/
theorem choose_odd_iff_land_eq (a b : ℕ) :
    Odd (Nat.choose b a) ↔ a &&& b = a := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a; simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [choose_odd_recur, and_eq_recur, ih (a / 2) hsmall]

private theorem subset_add_iff_and_zero (a b : ℕ) :
    a &&& (a + b) = a ↔ a &&& b = 0 := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a; simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [and_eq_recur, and_zero_recur]
      by_cases hoverlap : a % 2 = 1 ∧ b % 2 = 1
      · have hlow : ¬ a % 2 ≤ (a + b) % 2 := by omega
        have hz : ¬ (a % 2 = 0 ∨ b % 2 = 0) := by omega
        simp only [hlow, hz, false_and]
      · have hlow : a % 2 ≤ (a + b) % 2 := by omega
        have hz : a % 2 = 0 ∨ b % 2 = 0 := by omega
        have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        rw [hdiv]
        simp only [hlow, hz, true_and]
        exact ih (a / 2) hsmall (b / 2)

/-- Kummer's carry theorem at `p = 2`: `Nat.choose (a + b) a` is odd iff `a &&& b = 0`. -/
theorem choose_add_odd_iff_land_eq_zero (a b : ℕ) :
    Odd (Nat.choose (a + b) a) ↔ a &&& b = 0 := by
  rw [choose_odd_iff_land_eq]
  exact subset_add_iff_and_zero a b

theorem mask_iff_land_eq (a b : ℕ) :
    mask a b ↔ a &&& b = a := by
  simp only [mask, exists_eq_left, odd_witness_iff_odd, choose_odd_iff_land_eq]

theorem orthogonal_iff_land_eq_zero (a b : ℕ) :
    orthogonal a b ↔ a &&& b = 0 := by
  simp only [orthogonal, exists_eq_left, odd_witness_iff_odd,
    choose_add_odd_iff_land_eq_zero]

private theorem add_eq_or_add_and (a b : ℕ) :
    a + b = (a ||| b) + (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a; simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      have h := ih (a / 2) hsmall (b / 2)
      have hand := Nat.and_div_two (a := a) (b := b)
      have hor := Nat.or_div_two (a := a) (b := b)
      have handmod := Nat.and_mod_two_eq_one (a := a) (b := b)
      have hormod := Nat.or_mod_two_eq_one (a := a) (b := b)
      omega

private theorem add_eq_or_of_and_zero (a b : ℕ) (h : a &&& b = 0) :
    a + b = a ||| b := by
  simpa only [h, Nat.add_zero] using add_eq_or_add_and a b

private theorem disjoint_union_and (z a b : ℕ)
    (ha : z &&& a = 0) (hb : z &&& b = 0) (hab : a &&& b = 0) :
    (z ||| a) &&& (z ||| b) = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  have ha' := congrArg (fun n : ℕ => n.testBit i) ha
  have hb' := congrArg (fun n : ℕ => n.testBit i) hb
  have hab' := congrArg (fun n : ℕ => n.testBit i) hab
  simp only [Nat.testBit_and, Nat.zero_testBit] at ha' hb' hab'
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases hz : z.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp_all

private theorem and_ldiff_left (x y : ℕ) : (x &&& y) &&& Nat.ldiff x y = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem and_ldiff_right (x y : ℕ) : (x &&& y) &&& Nat.ldiff y x = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem ldiff_and_ldiff (x y : ℕ) : Nat.ldiff x y &&& Nat.ldiff y x = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem or_ldiff_left (x y : ℕ) : (x &&& y) ||| Nat.ldiff x y = x := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_ldiff]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem or_ldiff_right (x y : ℕ) : (x &&& y) ||| Nat.ldiff y x = y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_ldiff]
  cases x.testBit i <;> cases y.testBit i <;> rfl

theorem bit_and_iff_land_eq (z x y : ℕ) :
    bit_and z x y ↔ z = x &&& y := by
  constructor
  · rintro ⟨a, b, hx, hy, ha, hb, hab⟩
    have ha' := (orthogonal_iff_land_eq_zero z a).mp ha
    have hb' := (orthogonal_iff_land_eq_zero z b).mp hb
    have hab' := (orthogonal_iff_land_eq_zero a b).mp hab
    rw [hx, hy, add_eq_or_of_and_zero z a ha', add_eq_or_of_and_zero z b hb']
    exact (disjoint_union_and z a b ha' hb' hab').symm
  · rintro rfl
    refine ⟨Nat.ldiff x y, Nat.ldiff y x, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((add_eq_or_of_and_zero (x &&& y) (Nat.ldiff x y) (and_ldiff_left x y)).trans
        (or_ldiff_left x y)).symm
    · exact ((add_eq_or_of_and_zero (x &&& y) (Nat.ldiff y x) (and_ldiff_right x y)).trans
        (or_ldiff_right x y)).symm
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (and_ldiff_left x y)
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (and_ldiff_right x y)
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (ldiff_and_ldiff x y)

/-! ## 2. Unique Dyadic Base Selection -/

/-- For `L > 0`, `e` is the unique dyadic exponent satisfying `2^e ≤ L < 2^(e+1)`. -/
def IsDyadicHalfBase (L e : ℕ) : Prop :=
  2 ^ e ≤ L ∧ L < 2 ^ (e + 1)

theorem pow2_pos (e : ℕ) : 0 < 2 ^ e := by
  induction e with
  | zero => decide
  | succ _ ih => rw [Nat.pow_succ]; omega

theorem pow2_mono_lt {a b : ℕ} (h : a < b) : 2 ^ (a + 1) ≤ 2 ^ b := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hk : a = k
    · subst hk; exact le_refl _
    · have := ih (by omega); rw [Nat.pow_succ]; omega

theorem dyadic_exponent_unique (L e₁ e₂ : ℕ)
    (h₁ : IsDyadicHalfBase L e₁) (h₂ : IsDyadicHalfBase L e₂) : e₁ = e₂ := by
  rcases h₁ with ⟨h1_le, h1_lt⟩
  rcases h₂ with ⟨h2_le, h2_lt⟩
  by_cases hlt : e₁ < e₂
  · have := pow2_mono_lt hlt; omega
  · by_cases hgt : e₂ < e₁
    · have := pow2_mono_lt hgt; omega
    · omega

theorem dyadic_exponent_exists (L : ℕ) (hL : 0 < L) :
    ∃ e : ℕ, IsDyadicHalfBase L e := by
  induction L using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn1 : n = 1
    · subst hn1; exact ⟨0, by decide, by decide⟩
    · obtain ⟨e, he_le, he_lt⟩ := ih (n / 2) (Nat.div_lt_self hL (by decide)) (by omega)
      refine ⟨e + 1, ?_, ?_⟩
      · rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ 2 (e + 1)]; omega

/-! ## 3. Carry-Free Base-`B` Computation History Packing (`Finset.sum` & `packHistory`) -/

/-- Recursive base-`B` history polynomial evaluation `∑_{t=0}^{n-1} f(t) * B^t`. -/
def packHistory (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f 0 + B * packHistory B (fun t => f (t + 1)) n

/-- Equivalence between `packHistory B f n` and Mathlib's `∑ t ∈ Finset.range n, f t * B ^ t`. -/
theorem packHistory_eq_finset_sum (B : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    packHistory B f n = ∑ t ∈ Finset.range n, f t * B ^ t := by
  induction n generalizing f with
  | zero => simp [packHistory]
  | succ k ih =>
    unfold packHistory
    rw [ih (fun t => f (t + 1)), Finset.sum_range_succ', pow_zero, mul_one,
      Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)

theorem digit_split {B a₀ b₀ A B' : ℕ} (ha : a₀ < B) (hb : b₀ < B) :
    a₀ + B * A = b₀ + B * B' ↔ a₀ = b₀ ∧ A = B' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have hB : 0 < B := by omega
  have hmod : (a₀ + B * A) % B = (b₀ + B * B') % B := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  subst hmod
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hB (by omega)⟩

private theorem digit_split_right {M a b x y : ℕ} (ha : a < M) (hb : b < M)
    (h : a + x * M = b + y * M) : a = b ∧ x = y := by
  exact (digit_split ha hb).mp (by linarith)

/-- Uniqueness of Finset base-`B` expansions with an arbitrary top part. -/
theorem digits_eq_of_sum_eq {B : ℕ} (u v : ℕ → ℕ) (n : ℕ) :
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
    have key : (∑ t ∈ Finset.range n, u t * B ^ t) + (u n + x * B) * B ^ n
        = (∑ t ∈ Finset.range n, v t * B ^ t) + (v n + y * B) * B ^ n :=
      e1.symm.trans (h.trans e2)
    obtain ⟨hlow, htop⟩ := ih (u n + x * B) (v n + y * B)
      (fun t ht => hu t (by omega)) (fun t ht => hv t (by omega)) key
    obtain ⟨hn, hxy⟩ := digit_split_right (hu n (by omega)) (hv n (by omega)) htop
    refine ⟨fun t ht => ?_, hxy⟩
    by_cases htn : t < n
    · exact hlow t htn
    · have htn' : t = n := by omega
      rw [htn']; exact hn

/-- Carry-free decoding of the packed register equation `R + B*C = init + B*R + B*A`
    over `Finset.range (q + 1)` (matching `ZInQ.PackedHistory.packed_register_decode`). -/
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
  have hρ0 : ρ 0 < B := Nat.lt_trans (hρ 0 (Nat.zero_le q)) hKB
  have hinitB : init < B := Nat.lt_trans hinit hKB
  obtain ⟨h0, h2⟩ := digit_split_right hρ0 hinitB h1
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
  have h3 : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t) + γ q * B ^ q
      = (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t) + (ρ q + α q) * B ^ q :=
    e1.trans (h2.trans e2.symm)
  have hu : ∀ t, t < q → ρ (t+1) + γ t < B := by
    intro t ht; have := hρ (t+1) (by omega); have := hγ t (by omega); omega
  have hv : ∀ t, t < q → ρ t + α t < B := by
    intro t ht; have := hρ t (by omega); have := hα t (by omega); omega
  obtain ⟨hstep, hlast⟩ := digits_eq_of_sum_eq (fun t => ρ (t+1) + γ t)
    (fun t => ρ t + α t) q (γ q) (ρ q + α q) hu hv h3
  exact ⟨h0, hstep, hlast⟩

theorem packHistory_lt_pow (B : ℕ) (f : ℕ → ℕ) (n : ℕ)
    (_hB : 0 < B) (hf : ∀ t, t < n → f t < B) :
    packHistory B f n < B ^ n := by
  induction n generalizing f with
  | zero => simp [packHistory]
  | succ k ih =>
    unfold packHistory
    have hf0 : f 0 < B := hf 0 (Nat.zero_lt_succ k)
    have hfk := ih (fun t => f (t + 1)) (fun t ht => hf (t + 1) (Nat.succ_lt_succ ht))
    have hpow : B ^ (k + 1) = B * B ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have hmul := Nat.mul_le_mul_left B (show packHistory B (fun t => f (t + 1)) k + 1 ≤ B ^ k by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem packHistory_eq_iff (B : ℕ) (f g : ℕ → ℕ) (n : ℕ)
    (hf : ∀ t, t < n → f t < B) (hg : ∀ t, t < n → g t < B) :
    packHistory B f n = packHistory B g n ↔ ∀ t, t < n → f t = g t := by
  induction n generalizing f g with
  | zero => simp [packHistory]
  | succ k ih =>
    unfold packHistory
    rw [digit_split (hf 0 (Nat.zero_lt_succ k)) (hg 0 (Nat.zero_lt_succ k))]
    rw [ih (fun t => f (t + 1)) (fun t => g (t + 1))
        (fun t ht => hf (t + 1) (Nat.succ_lt_succ ht))
        (fun t ht => hg (t + 1) (Nat.succ_lt_succ ht))]
    refine ⟨by rintro ⟨h0, hsucc⟩ t ht; cases t with
               | zero => exact h0
               | succ m => exact hsucc m (Nat.lt_of_succ_lt_succ ht),
            fun h => ⟨h 0 (Nat.zero_lt_succ k), fun t ht => h (t + 1) (Nat.succ_lt_succ ht)⟩⟩

theorem packHistory_add (B : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    packHistory B (fun t => f t + g t) n = packHistory B f n + packHistory B g n := by
  induction n generalizing f g with
  | zero => simp [packHistory]
  | succ k ih =>
    unfold packHistory
    rw [ih (fun t => f (t + 1)) (fun t => g (t + 1)), Nat.mul_add]
    omega

theorem packHistory_succ (B : ℕ) (ρ : ℕ → ℕ) (q : ℕ) :
    packHistory B ρ (q + 1) = ρ 0 + B * packHistory B (fun t => ρ (t + 1)) q :=
  rfl

def extendSlot (q : ℕ) (f : ℕ → ℕ) (lastVal : ℕ) (t : ℕ) : ℕ :=
  if t < q then f t else lastVal

theorem packHistory_extendSlot (B : ℕ) (q : ℕ) (f : ℕ → ℕ) (lastVal : ℕ) :
    packHistory B f q + lastVal * B ^ q = packHistory B (extendSlot q f lastVal) (q + 1) := by
  induction q generalizing f with
  | zero => simp [packHistory, extendSlot]
  | succ k ih =>
    unfold packHistory
    have h0 : extendSlot (k + 1) f lastVal 0 = f 0 := by simp [extendSlot]
    have hshift : (fun t => extendSlot (k + 1) f lastVal (t + 1)) =
        extendSlot k (fun t => f (t + 1)) lastVal := by
      funext t; unfold extendSlot
      by_cases htk : t < k
      · simp [htk, Nat.succ_lt_succ htk]
      · simp [htk, show ¬ (t + 1 < k + 1) from fun h => htk (Nat.lt_of_succ_lt_succ h)]
    rw [h0, hshift, ← ih (fun t => f (t + 1)), Nat.pow_succ, Nat.mul_comm (B ^ k) B,
        ← Nat.mul_assoc, Nat.mul_comm lastVal B, Nat.mul_assoc, Nat.mul_add]
    omega

/-- Global base-`B` telescoping recurrence extracting both the step relation
    `ρ(t+1) + dec(t) = ρ(t) + inc(t)` and the terminal value `ρ_last = ρ(q)`. -/
theorem signed_recurrence_iff (B q init ρ_last : ℕ)
    (ρ inc dec : ℕ → ℕ)
    (hinit : init < B) (hρ0 : ρ 0 < B) (hlast : ρ_last < B) (hρq : ρ q < B)
    (hlhs : ∀ t, t < q → ρ (t + 1) + dec t < B)
    (hrhs : ∀ t, t < q → ρ t + inc t < B) :
    let R := packHistory B ρ (q + 1)
    let Inc := packHistory B inc q
    let Dec := packHistory B dec q
    R + B * (Dec + ρ_last * B ^ q) = init + B * (R + Inc) ↔
      (ρ 0 = init ∧
       (∀ t, t < q → ρ (t + 1) + dec t = ρ t + inc t) ∧
       ρ_last = ρ q) := by
  intro R Inc Dec
  have hL : R + B * (Dec + ρ_last * B ^ q) =
      ρ 0 + B * (packHistory B (extendSlot q (fun t => ρ (t + 1) + dec t) ρ_last) (q + 1)) := by
    dsimp [R, Dec]
    rw [packHistory_succ B ρ q,
        ← packHistory_extendSlot B q (fun t => ρ (t + 1) + dec t) ρ_last,
        packHistory_add B (fun t => ρ (t + 1)) dec q, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega
  have hR : init + B * (R + Inc) =
      init + B * (packHistory B (extendSlot q (fun t => ρ t + inc t) (ρ q)) (q + 1)) := by
    dsimp [R, Inc]
    have hR_split : packHistory B ρ (q + 1) = packHistory B ρ q + ρ q * B ^ q := by
      rw [packHistory_extendSlot B q ρ (ρ q)]
      apply (packHistory_eq_iff B ρ (extendSlot q ρ (ρ q)) (q + 1)
        (fun t ht => by
          by_cases h : t < q
          · have := hrhs t h; omega
          · have hq_eq : t = q := by omega
            subst hq_eq; exact hρq)
        (fun t _ => by
          unfold extendSlot
          by_cases h : t < q
          · simp [h]; have := hrhs t h; omega
          · simp [h]; exact hρq)).mpr
      intro t ht; unfold extendSlot
      by_cases h : t < q
      · simp [h]
      · have : t = q := by omega
        subst this; simp
    rw [hR_split, ← packHistory_extendSlot B q (fun t => ρ t + inc t) (ρ q),
        packHistory_add B ρ inc q, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega
  rw [hL, hR, digit_split hρ0 hinit]
  rw [packHistory_eq_iff B
      (extendSlot q (fun t => ρ (t + 1) + dec t) ρ_last)
      (extendSlot q (fun t => ρ t + inc t) (ρ q))
      (q + 1)
      (fun t _ => by
        unfold extendSlot
        by_cases h : t < q
        · simp [h]; exact hlhs t h
        · simp [h]; exact hlast)
      (fun t _ => by
        unfold extendSlot
        by_cases h : t < q
        · simp [h]; exact hrhs t h
        · simp [h]; exact hρq)]
  constructor
  · rintro ⟨h0, hslots⟩
    refine ⟨h0, fun t ht => ?_, ?_⟩
    · have := hslots t (Nat.lt_succ_of_lt ht); unfold extendSlot at this; simp [ht] at this; exact this
    · have := hslots q (Nat.lt_succ_self q); unfold extendSlot at this; simp at this; exact this
  · rintro ⟨h0, hstep, hq⟩
    refine ⟨h0, fun t ht => ?_⟩
    unfold extendSlot
    by_cases h : t < q
    · simp [h, hstep t h]
    · have : t = q := by omega
      subst this; simp [hq]

/-! ## 4. Single-Fold Complement-Mask & Disjointness-in-`D` Binomial Mask Equivalence -/

/-- Slotwise complement-mask zero test: for `z_t ∈ {0, 1}` and `r_t &&& (2^w - 1) = r_t`,
    `r_t &&& ((2^w - 1) * (1 - z_t)) = r_t ↔ (z_t = 1 → r_t = 0)`. -/
theorem complement_mask_slot_zero_test (w r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t) :
    let v_t := 1 - z_t
    r_t &&& ((2 ^ w - 1) * v_t) = r_t ↔ (z_t = 1 → r_t = 0) := by
  intro v_t
  rcases hz with rfl | rfl
  · simp [v_t, hr_mask]
  · simp only [v_t, Nat.sub_self, Nat.mul_zero, Nat.and_zero, true_implies]
    exact ⟨Eq.symm, Eq.symm⟩

/-- Direct binomial `mask` (`Odd (Nat.choose ...)`) version of the Stage 1 complement-mask zero test,
    proved via Lucas's theorem (`mask_iff_land_eq`). -/
theorem complement_mask_iff_zero_test (w r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : mask r_t (2 ^ w - 1)) :
    mask r_t ((2 ^ w - 1) * (1 - z_t)) ↔ (z_t = 1 → r_t = 0) := by
  rw [mask_iff_land_eq] at hr_mask ⊢
  exact complement_mask_slot_zero_test w r_t z_t hz hr_mask

theorem recurrence_prevents_underflow (r_t r_next v_t : ℕ)
    (hstep : r_next + v_t = r_t) :
    v_t = 1 → 1 ≤ r_t := by
  intro; omega

/-- Complete correctness of single-fold zero/nonzero branching for a counter decrement
    at slot `t` with zero `bitAnd` calls and zero `N_j` variables. -/
theorem single_fold_branch_correct (w r_t r_next s_t v_t z_t : ℕ)
    (_hs : s_t = 0 ∨ s_t = 1) (_hv : v_t = 0 ∨ v_t = 1) (hz : z_t = 0 ∨ z_t = 1)
    (hpart : s_t = v_t + z_t)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t)
    (hzero_guard : r_t &&& ((2 ^ w - 1) * (1 - z_t)) = r_t)
    (hstep : r_next + v_t = r_t) :
    (s_t = 0 → v_t = 0 ∧ z_t = 0 ∧ r_next = r_t) ∧
    (s_t = 1 ∧ r_t = 0 → v_t = 0 ∧ z_t = 1 ∧ r_next = 0) ∧
    (s_t = 1 ∧ 0 < r_t → v_t = 1 ∧ z_t = 0 ∧ r_next = r_t - 1) := by
  have hz_imp := (complement_mask_slot_zero_test w r_t z_t hz hr_mask).mp hzero_guard
  refine ⟨by intro; omega, by rintro ⟨_, _⟩; omega, ?_⟩
  rintro ⟨_, _⟩
  rcases hz with rfl | rfl
  · omega
  · have := hz_imp rfl; omega

/-- For any `c : ℕ`, `a` is a bitwise submask of `2^c - 1` (`a &&& (2^c - 1) = a`)
    if and only if `a ≤ 2^c - 1`. -/
theorem land_two_pow_sub_one_eq_self_iff (c a : ℕ) :
    a &&& (2 ^ c - 1) = a ↔ a ≤ 2 ^ c - 1 := by
  have hpos := pow2_pos c
  have hmod : a &&& (2 ^ c - 1) = a % 2 ^ c := Nat.and_two_pow_sub_one_eq_mod a c
  rw [hmod]
  constructor
  · intro h
    have hlt : a % 2 ^ c < 2 ^ c := Nat.mod_lt a hpos
    omega
  · intro h
    exact Nat.mod_eq_of_lt (by omega)

/-- Stage 2 Disjointness-in-`D` binomial-mask theorem via Lucas's theorem (`mask_iff_land_eq`):
    for a slot capacity `K = 2^c` and binary indicator `z ∈ {0, 1}`, a single binomial
    `mask (r + (2^c - 1) * z) (2^c - 1)` simultaneously enforces the register bound
    `mask r (2^c - 1)` (`r ≤ 2^c - 1`) and the zero-test implication `z = 1 → r = 0`. -/
theorem disjoint_in_D_mask_iff (c r z : ℕ) (hz : z = 0 ∨ z = 1) :
    mask (r + (2 ^ c - 1) * z) (2 ^ c - 1) ↔
      (mask r (2 ^ c - 1) ∧ (z = 1 → r = 0)) := by
  rw [mask_iff_land_eq, mask_iff_land_eq,
      land_two_pow_sub_one_eq_self_iff, land_two_pow_sub_one_eq_self_iff]
  rcases hz with rfl | rfl
  · simp
  · omega

end DiophantineZQ
