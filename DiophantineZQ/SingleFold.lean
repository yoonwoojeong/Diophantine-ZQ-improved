/-
  DiophantineZQ.SingleFold
  ========================
  Formalization of large-base computation-history encoding and single-fold witness
  compression (following OpenAI's Single-fold Diophantine Representations, Sept 2026):
  1. Unique dyadic base selection (`dyadic_exponent_unique`, `dyadic_exponent_exists`).
  2. Carry-free base-`B` digit splitting and history uniqueness (`digit_split`, `packHistory_eq_iff`).
  3. Signed counter recurrence and terminal value extraction (`signed_recurrence_iff`).
  4. Single-fold complement-mask zero testing (`complement_mask_slot_zero_test`, `single_fold_branch_correct`).
-/

import DiophantineZQ.Domains

namespace DiophantineZQ

/-! ## 1. Unique Dyadic Base Selection -/

/-- For `L > 0`, `e` is the unique dyadic exponent satisfying `2^e ≤ L < 2^(e+1)`. -/
def IsDyadicHalfBase (L e : Nat) : Prop :=
  2 ^ e ≤ L ∧ L < 2 ^ (e + 1)

theorem pow2_pos (e : Nat) : 0 < 2 ^ e := by
  induction e with
  | zero => decide
  | succ _ ih => rw [Nat.pow_succ]; omega

theorem pow2_mono_lt {a b : Nat} (h : a < b) : 2 ^ (a + 1) ≤ 2 ^ b := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hk : a = k
    · subst hk; exact Nat.le_refl _
    · have := ih (by omega); rw [Nat.pow_succ]; omega

theorem dyadic_exponent_unique (L e₁ e₂ : Nat)
    (h₁ : IsDyadicHalfBase L e₁) (h₂ : IsDyadicHalfBase L e₂) : e₁ = e₂ := by
  rcases h₁ with ⟨h1_le, h1_lt⟩
  rcases h₂ with ⟨h2_le, h2_lt⟩
  by_cases hlt : e₁ < e₂
  · have := pow2_mono_lt hlt; omega
  · by_cases hgt : e₂ < e₁
    · have := pow2_mono_lt hgt; omega
    · omega

theorem dyadic_exponent_exists (L : Nat) (hL : 0 < L) :
    ∃ e : Nat, IsDyadicHalfBase L e := by
  induction L using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn1 : n = 1
    · subst hn1; exact ⟨0, by decide, by decide⟩
    · obtain ⟨e, he_le, he_lt⟩ := ih (n / 2) (Nat.div_lt_self hL (by decide)) (by omega)
      refine ⟨e + 1, ?_, ?_⟩
      · rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ 2 (e + 1)]; omega

/-! ## 2. Carry-Free Base-`B` Computation History Packing -/

/-- `packHistory B f n = ∑_{t=0}^{n-1} f(t) * B^t`. -/
def packHistory (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 + B * packHistory B (fun t => f (t + 1)) n

theorem digit_split {B a₀ b₀ A B' : Nat} (ha : a₀ < B) (hb : b₀ < B) :
    a₀ + B * A = b₀ + B * B' ↔ a₀ = b₀ ∧ A = B' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have hB : 0 < B := by omega
  have hmod : (a₀ + B * A) % B = (b₀ + B * B') % B := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  subst hmod
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hB (by omega)⟩

theorem packHistory_lt_pow (B : Nat) (f : Nat → Nat) (n : Nat)
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

theorem packHistory_eq_iff (B : Nat) (f g : Nat → Nat) (n : Nat)
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

theorem packHistory_add (B : Nat) (f g : Nat → Nat) (n : Nat) :
    packHistory B (fun t => f t + g t) n = packHistory B f n + packHistory B g n := by
  induction n generalizing f g with
  | zero => simp [packHistory]
  | succ k ih =>
    unfold packHistory
    rw [ih (fun t => f (t + 1)) (fun t => g (t + 1)), Nat.mul_add]
    omega

/-! ## 3. Single-Fold Signed Counter Recurrence Without Cleanup Loop -/

theorem packHistory_succ (B : Nat) (ρ : Nat → Nat) (q : Nat) :
    packHistory B ρ (q + 1) = ρ 0 + B * packHistory B (fun t => ρ (t + 1)) q :=
  rfl

def extendSlot (q : Nat) (f : Nat → Nat) (lastVal : Nat) (t : Nat) : Nat :=
  if t < q then f t else lastVal

theorem packHistory_extendSlot (B : Nat) (q : Nat) (f : Nat → Nat) (lastVal : Nat) :
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
theorem signed_recurrence_iff (B q init ρ_last : Nat)
    (ρ inc dec : Nat → Nat)
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
    · have := hslots q (Nat.lt_succ_self q); unfold extendSlot at this; simp [Nat.lt_irrefl q] at this; exact this
  · rintro ⟨h0, hstep, hq⟩
    refine ⟨h0, fun t ht => ?_⟩
    unfold extendSlot
    by_cases h : t < q
    · simp [h, hstep t h]
    · have : t = q := by omega
      subst this; simp [h, hq]

/-! ## 4. Single-Fold Complement-Mask Zero Test -/

/-- Slotwise complement-mask zero test: for `z_t ∈ {0, 1}` and `r_t &&& (2^w - 1) = r_t`,
    `r_t &&& ((2^w - 1) * (1 - z_t)) = r_t ↔ (z_t = 1 → r_t = 0)`. -/
theorem complement_mask_slot_zero_test (w r_t z_t : Nat)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t) :
    let v_t := 1 - z_t
    r_t &&& ((2 ^ w - 1) * v_t) = r_t ↔ (z_t = 1 → r_t = 0) := by
  intro v_t
  rcases hz with rfl | rfl
  · simp [v_t, hr_mask]
  · simp only [v_t, Nat.sub_self, Nat.mul_zero, Nat.and_zero, true_implies]
    exact ⟨Eq.symm, Eq.symm⟩

theorem recurrence_prevents_underflow (r_t r_next v_t : Nat)
    (hstep : r_next + v_t = r_t) :
    v_t = 1 → 1 ≤ r_t := by
  intro; omega

/-- Complete correctness of single-fold zero/nonzero branching for a counter decrement
    at slot `t` with zero `bitAnd` calls and zero `N_j` variables. -/
theorem single_fold_branch_correct (w r_t r_next s_t v_t z_t : Nat)
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

end DiophantineZQ
