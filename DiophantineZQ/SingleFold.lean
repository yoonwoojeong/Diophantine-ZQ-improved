/-
  DiophantineZQ.SingleFold
  ========================
  Formalization of large-base computation-history encoding and single-fold witness
  compression (following OpenAI's Single-fold Diophantine Representations, Sept 2026,
  and contrasting with the `integer-diophantine-compiler.js` architecture in
  `diophantine-z-q`).

  Key results proved here in core Lean 4 with zero `sorry`:
  1. Unique Dyadic Base Selection (`dyadic_base_unique`):
     For any positive clock end `L = C + T > 0`, the inequalities `b ≤ L` and `2 * L < 4 * b`
     with `b = 2^(w - 2)` uniquely determine the power-of-two base `B = 4 * b = 2^w`.
  2. Carry-Free Base-`B` Digit Uniqueness (`digit_split`, `packHistory_eq_iff`):
     Packing a finite sequence of length `q + 1` in base `B` where digits lie in `[0, B)`
     uniquely determines every step digit `0 ≤ t ≤ q`.
  3. Signed Counter Recurrence & Terminal Value Extraction Without Cleanup
     (`signed_recurrence_iff`):
     The single-fold equation `R + B * (J_last + Dec) = init + B * (R + Inc)` with
     digits `< B` uniquely forces `ρ(0) = init`, `ρ(t+1) + dec(t) = ρ(t) + inc(t)` for
     `t < q`, AND extracts the terminal value `ρ(q) = ρ_last` directly from the `B^q`
     coefficient—avoiding any post-halt register cleanup loop!
  4. Complement-Mask Zero Testing (`complement_mask_zero_test_iff`):
     Replacing `diophantine-z-q`'s `bitAnd`-based nonzero indicator `K * N_j = (R_j + D) &&& (K * F_q)`
     and branch `V_i = S_i &&& N_j` (which costs 3 `orthogonal` = 9 `power` calls per `bitAnd`!)
     with the single-fold complement mask `Z_i + V_i = M` and `R_j ≼ (B - 1) * V_i`
     tests `ρ_j(t) = 0` at active zero-branch slots using ONLY ONE `mask` (`≼`) call per
     decrement/zero-test and ZERO `bitAnd` calls.
-/

import DiophantineZQ.Domains

namespace DiophantineZQ

/-! ## 1. Unique Dyadic Base Selection (Single-Fold Lemma 4.2) -/

/-- The dyadic interval condition from OpenAI's Single-fold Diophantine Representations:
    Given a positive target `L > 0` (such as the terminal clock value `ρ_0 = C + T`),
    a power of two `b = 2^e` satisfies `b ≤ L ∧ 2 * L < 4 * b` (i.e. `b ≤ L < 2 * b`). -/
def IsDyadicHalfBase (L e : Nat) : Prop :=
  2 ^ e ≤ L ∧ L < 2 ^ (e + 1)

theorem pow2_pos (e : Nat) : 0 < 2 ^ e := by
  induction e with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem pow2_mono_lt {a b : Nat} (h : a < b) : 2 ^ (a + 1) ≤ 2 ^ b := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hk : a = k
    · subst hk
      exact Nat.le_refl _
    · have hlt : a < k := by omega
      have h1 := ih hlt
      rw [Nat.pow_succ]
      omega

/-- Uniqueness of the dyadic exponent `e` (and hence uniqueness of `b = 2^e` and
    `B = 4 * b = 2^(e + 2)`): for any `L`, at most one exponent `e : Nat` satisfies
    `2^e ≤ L < 2^(e+1)`. This is why pinning the base `B` to the dyadic interval of
    the deterministic clock `ρ_0` guarantees single-fold (unique) witness selection. -/
theorem dyadic_exponent_unique (L e₁ e₂ : Nat)
    (h₁ : IsDyadicHalfBase L e₁) (h₂ : IsDyadicHalfBase L e₂) : e₁ = e₂ := by
  rcases h₁ with ⟨h1_le, h1_lt⟩
  rcases h₂ with ⟨h2_le, h2_lt⟩
  by_cases hlt : e₁ < e₂
  · have hpow := pow2_mono_lt hlt
    omega
  · by_cases hgt : e₂ < e₁
    · have hpow := pow2_mono_lt hgt
      omega
    · omega

/-- Existence of the dyadic exponent `e` for every `L > 0` (`Nat.log2 L`). -/
theorem dyadic_exponent_exists (L : Nat) (hL : 0 < L) :
    ∃ e : Nat, IsDyadicHalfBase L e := by
  induction L using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      exact ⟨0, by decide, by decide⟩
    · have hdiv_pos : 0 < n / 2 := by omega
      have hdiv_lt : n / 2 < n := Nat.div_lt_self hL (by decide)
      obtain ⟨e, he_le, he_lt⟩ := ih (n / 2) hdiv_lt hdiv_pos
      refine ⟨e + 1, ?_, ?_⟩
      · rw [Nat.pow_succ]
        omega
      · rw [Nat.pow_succ 2 (e + 1)]
        omega

/-! ## 2. Carry-Free Base-`B` Computation History Packing -/

/-- Pack a finite sequence `f : Nat → Nat` of length `n` into a base-`B` natural number:
    `packHistory B f n = ∑_{t=0}^{n-1} f(t) * B^t`. -/
def packHistory (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 + B * packHistory B (fun t => f (t + 1)) n

/-- Fundamental digit splitting lemma in base `B`: if `a₀ < B` and `b₀ < B`, then
    `a₀ + B * A = b₀ + B * B'` if and only if `a₀ = b₀ ∧ A = B'`. -/
theorem digit_split {B a₀ b₀ A B' : Nat} (ha : a₀ < B) (hb : b₀ < B) :
    a₀ + B * A = b₀ + B * B' ↔ a₀ = b₀ ∧ A = B' := by
  constructor
  · intro h
    have hB : 0 < B := by omega
    have hmod : (a₀ + B * A) % B = (b₀ + B * B') % B := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
    subst hmod
    have hCancel : B * A = B * B' := by omega
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hB hCancel⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Upper bound on a packed history whose digits are strictly below `K ≤ B`:
    `packHistory B f n < B^n`. -/
theorem packHistory_lt_pow (B : Nat) (f : Nat → Nat) (n : Nat)
    (_hB : 0 < B) (hf : ∀ t, t < n → f t < B) :
    packHistory B f n < B ^ n := by
  induction n generalizing f with
  | zero =>
    simp [packHistory]
  | succ k ih =>
    unfold packHistory
    have hf0 : f 0 < B := hf 0 (Nat.zero_lt_succ k)
    have hfk : packHistory B (fun t => f (t + 1)) k < B ^ k :=
      ih (fun t => f (t + 1)) (fun t ht => hf (t + 1) (Nat.succ_lt_succ ht))
    have hpow : B ^ (k + 1) = B * B ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have hle : packHistory B (fun t => f (t + 1)) k + 1 ≤ B ^ k := by omega
    have hmul : B * (packHistory B (fun t => f (t + 1)) k + 1) ≤ B * B ^ k :=
      Nat.mul_le_mul_left B hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-- Uniqueness of base-`B` packed histories: two bounded histories of length `n` have the
    same base-`B` packing if and only if they agree at every time step `t < n`. -/
theorem packHistory_eq_iff (B : Nat) (f g : Nat → Nat) (n : Nat)
    (hf : ∀ t, t < n → f t < B) (hg : ∀ t, t < n → g t < B) :
    packHistory B f n = packHistory B g n ↔ ∀ t, t < n → f t = g t := by
  induction n generalizing f g with
  | zero =>
    simp [packHistory]
  | succ k ih =>
    unfold packHistory
    have hf0 : f 0 < B := hf 0 (Nat.zero_lt_succ k)
    have hg0 : g 0 < B := hg 0 (Nat.zero_lt_succ k)
    rw [digit_split hf0 hg0]
    rw [ih (fun t => f (t + 1)) (fun t => g (t + 1))
        (fun t ht => hf (t + 1) (Nat.succ_lt_succ ht))
        (fun t ht => hg (t + 1) (Nat.succ_lt_succ ht))]
    constructor
    · rintro ⟨h0, hsucc⟩ t ht
      cases t with
      | zero => exact h0
      | succ m => exact hsucc m (Nat.lt_of_succ_lt_succ ht)
    · intro h
      refine ⟨h 0 (Nat.zero_lt_succ k), fun t ht => h (t + 1) (Nat.succ_lt_succ ht)⟩

theorem packHistory_add (B : Nat) (f g : Nat → Nat) (n : Nat) :
    packHistory B (fun t => f t + g t) n = packHistory B f n + packHistory B g n := by
  induction n generalizing f g with
  | zero =>
    simp [packHistory]
  | succ k ih =>
    unfold packHistory
    rw [ih (fun t => f (t + 1)) (fun t => g (t + 1)), Nat.mul_add]
    omega

/-! ## 3. Single-Fold Signed Counter Recurrence Without Cleanup Loop -/

/-- Helper shifting identity:
    `packHistory B ρ (q + 1) = ρ 0 + B * packHistory B (fun t => ρ (t + 1)) q`. -/
theorem packHistory_succ (B : Nat) (ρ : Nat → Nat) (q : Nat) :
    packHistory B ρ (q + 1) = ρ 0 + B * packHistory B (fun t => ρ (t + 1)) q :=
  rfl

/-- Appending a single top slot `lastVal * B^q` to a `q`-slot packed history gives a
    `(q + 1)`-slot packed history with `lastVal` at index `q`. -/
def extendSlot (q : Nat) (f : Nat → Nat) (lastVal : Nat) (t : Nat) : Nat :=
  if t < q then f t else lastVal

theorem packHistory_extendSlot (B : Nat) (q : Nat) (f : Nat → Nat) (lastVal : Nat) :
    packHistory B f q + lastVal * B ^ q = packHistory B (extendSlot q f lastVal) (q + 1) := by
  induction q generalizing f with
  | zero =>
    simp [packHistory, extendSlot]
  | succ k ih =>
    unfold packHistory
    have h0 : extendSlot (k + 1) f lastVal 0 = f 0 := by
      unfold extendSlot
      simp
    have hshift : (fun t => extendSlot (k + 1) f lastVal (t + 1)) =
        extendSlot k (fun t => f (t + 1)) lastVal := by
      funext t
      unfold extendSlot
      by_cases htk : t < k
      · have htk' : t + 1 < k + 1 := Nat.succ_lt_succ htk
        simp [htk, htk']
      · have htk' : ¬ (t + 1 < k + 1) := fun h => htk (Nat.lt_of_succ_lt_succ h)
        simp [htk, htk']
    rw [h0, hshift, ← ih (fun t => f (t + 1))]
    have hpow : B ^ (k + 1) = B * B ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, ← Nat.mul_assoc, Nat.mul_comm lastVal B, Nat.mul_assoc, Nat.mul_add]
    omega

/-- **Single-Fold Signed Counter Recurrence Theorem (Terminal Extraction Without Cleanup):**
    Suppose a counter trajectory `ρ : Nat → Nat` over `q + 1` steps (`0 ≤ t ≤ q`),
    increment indicator `inc : Nat → Nat` (`0 ≤ t < q`), and decrement indicator
    `dec : Nat → Nat` (`0 ≤ t < q`) have no carries in base `B`:
    - `init < B`
    - `ρ (t + 1) + dec t < B` for `t < q`
    - `ρ t + inc t < B` for `t < q`
    - `ρ_last < B` and `ρ q < B` (where at step `q` the machine halts so `inc q = dec q = 0`).
    Then the single-fold packed equation
      `R + B * (Dec + ρ_last * B^q) = init + B * (R + Inc)`
    holds if and only if:
    1. `ρ 0 = init` (initial condition),
    2. `∀ t < q, ρ (t + 1) + dec t = ρ t + inc t` (exact step-by-step recurrence), and
    3. `ρ_last = ρ q` (exact terminal register value extracted without clearing registers to 0!). -/
theorem signed_recurrence_iff (B q init ρ_last : Nat)
    (ρ inc dec : Nat → Nat)
    (hinit : init < B)
    (hρ0 : ρ 0 < B)
    (hlast : ρ_last < B)
    (hρq : ρ q < B)
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
    rw [packHistory_succ B ρ q]
    rw [← packHistory_extendSlot B q (fun t => ρ (t + 1) + dec t) ρ_last]
    rw [packHistory_add B (fun t => ρ (t + 1)) dec q]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
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
          · have : t = q := by omega
            subst this; exact hρq)
        (fun t ht => by
          unfold extendSlot
          by_cases h : t < q
          · simp [h]; have := hrhs t h; omega
          · simp [h]; exact hρq)).mpr
      intro t ht
      unfold extendSlot
      by_cases h : t < q
      · simp [h]
      · have : t = q := by omega
        subst this
        simp
    rw [hR_split]
    rw [← packHistory_extendSlot B q (fun t => ρ t + inc t) (ρ q)]
    rw [packHistory_add B ρ inc q]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega
  rw [hL, hR, digit_split hρ0 hinit]
  rw [packHistory_eq_iff B
      (extendSlot q (fun t => ρ (t + 1) + dec t) ρ_last)
      (extendSlot q (fun t => ρ t + inc t) (ρ q))
      (q + 1)
      (fun t ht => by
        unfold extendSlot
        by_cases h : t < q
        · simp [h]; exact hlhs t h
        · simp [h]; exact hlast)
      (fun t ht => by
        unfold extendSlot
        by_cases h : t < q
        · simp [h]; exact hrhs t h
        · simp [h]; exact hρq)]
  constructor
  · rintro ⟨h0, hslots⟩
    refine ⟨h0, fun t ht => ?_, ?_⟩
    · have := hslots t (Nat.lt_succ_of_lt ht)
      unfold extendSlot at this
      simp [ht] at this
      exact this
    · have := hslots q (Nat.lt_succ_self q)
      unfold extendSlot at this
      have hnot : ¬ (q < q) := Nat.lt_irrefl q
      simp [hnot] at this
      exact this
  · rintro ⟨h0, hstep, hq⟩
    refine ⟨h0, fun t ht => ?_⟩
    unfold extendSlot
    by_cases h : t < q
    · simp [h]
      exact hstep t h
    · have : t = q := by omega
      subst this
      simp [h, hq]

/-! ## 4. Single-Fold Complement-Mask Zero Test (Eliminating `bitAnd` / `N_j`) -/

/-- In `diophantine-z-q` (`integer-diophantine-compiler.js`), testing whether register `j`
    is zero at state `i` uses:
    - a global nonzero-indicator variable `N_j` per register, constrained by
      `K * N_j = (R_j + D) &&& (K * F_q)` (`bitAnd`, costing 2 witnesses + 3 `orthogonal` calls), and
    - per-instruction branch masks `V_i = S_i &&& N_j` and `S_i = V_i + W_i` (`bitAnd`,
      costing another 2 witnesses + 3 `orthogonal` calls).
    In OpenAI's Single-fold Diophantine representation (Proposition 5.3), both `N_j` and ALL
    `bitAnd` calls are eliminated by introducing the complement mask `V_q` (`Z_q + V_q = M`,
    so at slot `t`, `v_q(t) = 1 - z_q(t) ∈ {0, 1}`) and imposing the single mask relation
      `R_j ≼ (B - 1) * V_q`.
    At the digit level (for a single base-`B` digit `r_t < B` with `B = 2^w` and `z_t ∈ {0, 1}`),
    since `(B - 1) * (1 - z_t)` is either `B - 1` (all `w` bits set when `z_t = 0`) or `0`
    (all bits zero when `z_t = 1`), the bitwise mask condition
      `r_t &&& ((B - 1) * (1 - z_t)) = r_t`
    is equivalent to `z_t = 1 → r_t = 0`! -/
theorem complement_mask_slot_zero_test (w r_t z_t : Nat)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t) :
    let v_t := 1 - z_t
    r_t &&& ((2 ^ w - 1) * v_t) = r_t ↔ (z_t = 1 → r_t = 0) := by
  intro v_t
  rcases hz with rfl | rfl
  · dsimp [v_t]
    simp [hr_mask]
  · dsimp [v_t]
    simp only [Nat.and_zero, true_implies]
    constructor
    · intro h
      exact h.symm
    · intro h
      exact h.symm

/-- Furthermore, at a decrement branch `V_i` (where `S_i = V_i + Z_i`), the decrement
    cannot underflow a natural register `r_t` because the recurrence
    `r_{t+1} + v_t = r_t` with `r_{t+1} ≥ 0` ALREADY forces `v_t = 1 → r_t ≥ 1`!
    We prove this simple but critical arithmetic fact: -/
theorem recurrence_prevents_underflow (r_t r_next v_t : Nat)
    (hstep : r_next + v_t = r_t) :
    v_t = 1 → 1 ≤ r_t := by
  intro hv
  omega

/-- Combining `complement_mask_slot_zero_test` and `recurrence_prevents_underflow` yields
    the complete correctness of single-fold zero/nonzero branching for a counter decrement
    instruction at slot `t` with ZERO `bitAnd` calls and ZERO `N_j` variables: -/
theorem single_fold_branch_correct (w r_t r_next s_t v_t z_t : Nat)
    (_hs : s_t = 0 ∨ s_t = 1)
    (_hv : v_t = 0 ∨ v_t = 1)
    (hz : z_t = 0 ∨ z_t = 1)
    (hpart : s_t = v_t + z_t)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t)
    (hzero_guard : r_t &&& ((2 ^ w - 1) * (1 - z_t)) = r_t)
    (hstep : r_next + v_t = r_t) :
    (s_t = 0 → v_t = 0 ∧ z_t = 0 ∧ r_next = r_t) ∧
    (s_t = 1 ∧ r_t = 0 → v_t = 0 ∧ z_t = 1 ∧ r_next = 0) ∧
    (s_t = 1 ∧ 0 < r_t → v_t = 1 ∧ z_t = 0 ∧ r_next = r_t - 1) := by
  have hz_imp := (complement_mask_slot_zero_test w r_t z_t hz hr_mask).mp hzero_guard
  refine ⟨?_, ?_, ?_⟩
  · intro hs0
    omega
  · rintro ⟨hs1, hr0⟩
    omega
  · rintro ⟨hs1, hrpos⟩
    have hz0 : z_t = 0 := by
      rcases hz with hz0 | hz1
      · exact hz0
      · have := hz_imp hz1
        omega
    omega

end DiophantineZQ
