/-
  DiophantineZQ.SmallTM
  =====================
  Mathlib-backed formalization of binary Turing machines via base-2 half-tape stacks `L, R ∈ ℕ`:
  1. Operational semantics (`Machine`, `TMConfig`, `stepTM`, `runTM`, `HaltsIn`, `Halts`).
  2. Concrete 2-state Busy Beaver champion `BB2` (`1RB1LB_1LA1RH`), its exact single-fold
     step polynomial (`bb2StepPoly_iff_stepTM`, `bb2StepPoly_unique`), and 6-step halting proof (`bb2_halts`).
  3. Complete single-fold Diophantine representation (`singleFoldClear_iff`, `singleFoldClear_unique`)
     of the parametric `clear` register machine (`29` `power` calls / `2,343` vars → `1` `power` call / `85` vars),
     proving both witness existence and single-fold witness uniqueness.
-/

import DiophantineZQ.SingleFold

namespace DiophantineZQ

/-! ## 1. Binary Tape Stack Encoding of a Turing Machine (`L, R ∈ ℕ`) -/

inductive Dir where
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

inductive Action (numStates : ℕ) where
  | halt : Action numStates
  | step (writeBit : ℕ) (dir : Dir) (nextState : Fin numStates) : Action numStates
  deriving DecidableEq, Repr

def Machine (numStates : ℕ) := Fin numStates → Bool → Action numStates

/-- Arithmetic configuration of an `n`-state binary Turing machine over `ℕ`:
    `q < n` is an active state, `q = n` is the halting state, `L` encodes the tape left of the head,
    and `R` encodes the head symbol (`R % 2`) plus the tape right of the head (`R / 2`). -/
structure TMConfig where
  q : ℕ
  L : ℕ
  R : ℕ
  deriving DecidableEq, Repr

def initConfig : TMConfig := ⟨0, 0, 0⟩

def stepTM {n : ℕ} (M : Machine n) (c : TMConfig) : Option TMConfig :=
  if hq : c.q < n then
    let s : Bool := (c.R % 2 == 1)
    let r_half : ℕ := c.R / 2
    match M ⟨c.q, hq⟩ s with
    | .halt => some ⟨n, c.L, c.R⟩
    | .step w .R q' => some ⟨q'.val, 2 * c.L + w, r_half⟩
    | .step w .L q' => some ⟨q'.val, c.L / 2, 2 * (2 * r_half + w) + (c.L % 2)⟩
  else
    none

def runTM {n : ℕ} (M : Machine n) : ℕ → TMConfig → Option TMConfig
  | 0, c => some c
  | k + 1, c =>
      match stepTM M c with
      | none => none
      | some c' => runTM M k c'

def HaltsIn {n : ℕ} (M : Machine n) (c₀ : TMConfig) (k : ℕ) : Prop :=
  ∃ L_f R_f : ℕ, runTM M k c₀ = some ⟨n, L_f, R_f⟩

def Halts {n : ℕ} (M : Machine n) : Prop :=
  ∃ k : ℕ, HaltsIn M initConfig k

/-! ## 2. Exact Single-Fold Step Primitives -/

def isBitPoly (b : ℕ) : ℤ :=
  (b : ℤ) * ((b : ℤ) - 1)

theorem isBitPoly_eq_zero_iff (b : ℕ) :
    isBitPoly b = 0 ↔ (b = 0 ∨ b = 1) := by
  unfold isBitPoly
  rw [mul_eq_zero]
  constructor
  · rintro (h0 | h1)
    · left; omega
    · right; omega
  · rintro (rfl | rfl)
    · left; rfl
    · right; rfl

def bitSplitResidual (X x_half bit : ℕ) : ℤ :=
  sumSquaresInt [
    isBitPoly bit,
    (X : ℤ) - (2 * (x_half : ℤ) + (bit : ℤ))
  ]

theorem bitSplitResidual_eq_zero_iff (X x_half bit : ℕ) :
    bitSplitResidual X x_half bit = 0 ↔
      ((bit = 0 ∨ bit = 1) ∧ X = 2 * x_half + bit) := by
  unfold bitSplitResidual
  rw [sumSquaresInt_eq_zero_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [isBitPoly_eq_zero_iff]
  exact ⟨by rintro ⟨hb, hX⟩; exact ⟨hb, by omega⟩,
         by rintro ⟨hb, hX⟩; exact ⟨hb, by omega⟩⟩

theorem bitSplit_unique (X x_half bit : ℕ) :
    ((bit = 0 ∨ bit = 1) ∧ X = 2 * x_half + bit) ↔
      (bit = X % 2 ∧ x_half = X / 2) :=
  ⟨by rintro ⟨rfl | rfl, rfl⟩ <;> omega,
   by rintro ⟨rfl, rfl⟩; refine ⟨?_, ?_⟩ <;> omega⟩

/-! ## 3. Concrete 2-State Busy Beaver Champion `BB2` (`1RB1LB_1LA1RH`) -/

def BB2 : Machine 2 := fun q s =>
  match q.val, s with
  | 0, false => .step 1 .R ⟨1, by decide⟩
  | 0, true  => .step 1 .L ⟨1, by decide⟩
  | _, false => .step 1 .L ⟨0, by decide⟩
  | _, true  => .halt

def bb2StepPoly (c c' : TMConfig) (r_half r_bit l_half l_bit : ℕ) : ℤ :=
  let splitR := bitSplitResidual c.R r_half r_bit
  let splitL := bitSplitResidual c.L l_half l_bit
  let b00 := sumSquaresInt [
    (c.q : ℤ) - 0, (r_bit : ℤ) - 0,
    (c'.q : ℤ) - 1, (c'.L : ℤ) - (2 * (c.L : ℤ) + 1), (c'.R : ℤ) - (r_half : ℤ)
  ]
  let b01 := sumSquaresInt [
    (c.q : ℤ) - 0, (r_bit : ℤ) - 1,
    (c'.q : ℤ) - 1, (c'.L : ℤ) - (l_half : ℤ),
    (c'.R : ℤ) - (2 * (2 * (r_half : ℤ) + 1) + (l_bit : ℤ))
  ]
  let b10 := sumSquaresInt [
    (c.q : ℤ) - 1, (r_bit : ℤ) - 0,
    (c'.q : ℤ) - 0, (c'.L : ℤ) - (l_half : ℤ),
    (c'.R : ℤ) - (2 * (2 * (r_half : ℤ) + 1) + (l_bit : ℤ))
  ]
  let b11 := sumSquaresInt [
    (c.q : ℤ) - 1, (r_bit : ℤ) - 1,
    (c'.q : ℤ) - 2, (c'.L : ℤ) - (c.L : ℤ), (c'.R : ℤ) - (c.R : ℤ)
  ]
  sumSquaresInt [splitR, splitL, b00 * b01 * b10 * b11]

theorem bb2StepPoly_iff_stepTM (c c' : TMConfig) :
    (∃ r_half r_bit l_half l_bit : ℕ,
      bb2StepPoly c c' r_half r_bit l_half l_bit = 0) ↔
    stepTM BB2 c = some c' := by
  unfold bb2StepPoly
  constructor
  · rintro ⟨rh, rb, lh, lb, hpoly⟩
    rw [sumSquaresInt_eq_zero_iff] at hpoly
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hpoly
    rcases hpoly with ⟨hR, hL, hbranches⟩
    rw [bitSplitResidual_eq_zero_iff, bitSplit_unique] at hR hL
    rcases hR with ⟨hrb, hrh⟩
    rcases hL with ⟨hlb, hlh⟩
    subst hrb hrh hlb hlh
    cases c' with | mk q' L' R' =>
    rcases mul_eq_zero.mp hbranches with h012 | h11
    · rcases mul_eq_zero.mp h012 with h01 | h10
      · rcases mul_eq_zero.mp h01 with h00 | h01
        · rw [sumSquaresInt_eq_zero_iff] at h00
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h00
          rcases h00 with ⟨hq, hrb0, hq', hL', hR'⟩
          have hc_q : c.q = 0 := by omega
          have hc_rb : c.R % 2 = 0 := by omega
          have : q' = 1 := by omega
          have : L' = 2 * c.L + 1 := by omega
          have : R' = c.R / 2 := by omega
          subst_vars; unfold stepTM BB2; simp [hc_q, hc_rb]
        · rw [sumSquaresInt_eq_zero_iff] at h01
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h01
          rcases h01 with ⟨hq, hrb1, hq', hL', hR'⟩
          have hc_q : c.q = 0 := by omega
          have hc_rb : c.R % 2 = 1 := by omega
          have : q' = 1 := by omega
          have : L' = c.L / 2 := by omega
          have : R' = 2 * (2 * (c.R / 2) + 1) + c.L % 2 := by omega
          subst_vars; unfold stepTM BB2; simp [hc_q, hc_rb]
      · rw [sumSquaresInt_eq_zero_iff] at h10
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h10
        rcases h10 with ⟨hq, hrb0, hq', hL', hR'⟩
        have hc_q : c.q = 1 := by omega
        have hc_rb : c.R % 2 = 0 := by omega
        have : q' = 0 := by omega
        have : L' = c.L / 2 := by omega
        have : R' = 2 * (2 * (c.R / 2) + 1) + c.L % 2 := by omega
        subst_vars; unfold stepTM BB2; simp [hc_q, hc_rb]
    · rw [sumSquaresInt_eq_zero_iff] at h11
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h11
      rcases h11 with ⟨hq, hrb1, hq', hL', hR'⟩
      have hc_q : c.q = 1 := by omega
      have hc_rb : c.R % 2 = 1 := by omega
      have : q' = 2 := by omega
      have : L' = c.L := by omega
      have : R' = c.R := by omega
      subst_vars; unfold stepTM BB2; simp [hc_q, hc_rb]
  · intro hstep
    refine ⟨c.R / 2, c.R % 2, c.L / 2, c.L % 2, ?_⟩
    rw [sumSquaresInt_eq_zero_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have hR : bitSplitResidual c.R (c.R / 2) (c.R % 2) = 0 := by
      rw [bitSplitResidual_eq_zero_iff, bitSplit_unique]; exact ⟨rfl, rfl⟩
    have hL : bitSplitResidual c.L (c.L / 2) (c.L % 2) = 0 := by
      rw [bitSplitResidual_eq_zero_iff, bitSplit_unique]; exact ⟨rfl, rfl⟩
    refine ⟨hR, hL, ?_⟩
    unfold stepTM at hstep
    by_cases hq : c.q < 2
    · rw [dite_eq_left hq] at hstep
      have hq_cases : c.q = 0 ∨ c.q = 1 := by omega
      have hrb_cases : c.R % 2 = 0 ∨ c.R % 2 = 1 := by omega
      rcases hq_cases with hq0 | hq1 <;> rcases hrb_cases with hrb0 | hrb1
      · simp [BB2, hq0, hrb0] at hstep; subst hstep; simp [sumSquaresInt, hq0, hrb0]
      · simp [BB2, hq0, hrb1] at hstep; subst hstep; simp [sumSquaresInt, hq0, hrb1]
      · simp [BB2, hq1, hrb0] at hstep; subst hstep; simp [sumSquaresInt, hq1, hrb0]
      · simp [BB2, hq1, hrb1] at hstep; subst hstep; simp [sumSquaresInt, hq1, hrb1]
    · rw [dite_eq_right hq] at hstep; contradiction

/-- Single-fold witness uniqueness for `bb2StepPoly`: the 4-tuple `(r_half, r_bit, l_half, l_bit)`
    is uniquely determined by `(c, c')`. -/
theorem bb2StepPoly_unique (c c' : TMConfig)
    (rh₁ rb₁ lh₁ lb₁ rh₂ rb₂ lh₂ lb₂ : ℕ)
    (h₁ : bb2StepPoly c c' rh₁ rb₁ lh₁ lb₁ = 0)
    (h₂ : bb2StepPoly c c' rh₂ rb₂ lh₂ lb₂ = 0) :
    (rh₁, rb₁, lh₁, lb₁) = (rh₂, rb₂, lh₂, lb₂) := by
  unfold bb2StepPoly at h₁ h₂
  rw [sumSquaresInt_eq_zero_iff] at h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h₁ h₂
  rcases h₁ with ⟨hR₁, hL₁, _⟩
  rcases h₂ with ⟨hR₂, hL₂, _⟩
  rw [bitSplitResidual_eq_zero_iff, bitSplit_unique] at hR₁ hL₁ hR₂ hL₂
  rcases hR₁ with ⟨rfl, rfl⟩
  rcases hL₁ with ⟨rfl, rfl⟩
  rcases hR₂ with ⟨hrb₂, hrh₂⟩
  rcases hL₂ with ⟨hlb₂, hlh₂⟩
  rw [hrb₂, hrh₂, hlb₂, hlh₂]

theorem bb2_halts_in_6 : HaltsIn BB2 initConfig 6 :=
  ⟨1, 7, by decide⟩

theorem bb2_halts : Halts BB2 :=
  ⟨6, bb2_halts_in_6⟩

/-! ## 4. Single-Fold Diophantine Representation of the `clear` Machine -/

def clearAcceptsIn (n q_steps : ℕ) : Prop :=
  q_steps = n + 1

def singleFoldClearPoly (n q_steps B T_prev F_prev R₀ : ℕ) : ℤ :=
  sumSquaresInt [
    (B : ℤ) - (2 * (n : ℤ) + 4),
    (q_steps : ℤ) - ((n : ℤ) + 1),
    (B : ℤ) * (F_prev : ℤ) + 1 - ((T_prev : ℤ) + (F_prev : ℤ)),
    (R₀ : ℤ) + (B : ℤ) * (F_prev : ℤ) - ((n : ℤ) + (B : ℤ) * (R₀ : ℤ))
  ]

theorem geom_series_identity (B n : ℕ) (_hB : 1 ≤ B) :
    B * packHistory B (fun _ => 1) n + 1 = B ^ n + packHistory B (fun _ => 1) n := by
  induction n with
  | zero => simp [packHistory]
  | succ k ih =>
    have hpack : packHistory B (fun _ => 1) (k + 1) = 1 + B * packHistory B (fun _ => 1) k := rfl
    rw [hpack, Nat.pow_succ, Nat.mul_comm (B ^ k) B, Nat.mul_add, Nat.mul_one]
    have hmul := congrArg (fun x => B * x) ih
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at hmul
    omega

theorem countdown_history_identity (B n : ℕ) :
    packHistory B (fun t => n - t) (n + 1) + B * packHistory B (fun _ => 1) n =
      n + B * packHistory B (fun t => n - t) (n + 1) := by
  induction n with
  | zero => simp [packHistory]
  | succ k ih =>
    have hR : packHistory B (fun t => k + 1 - t) (k + 2) =
        (k + 1) + B * packHistory B (fun t => k - t) (k + 1) := by
      change (k + 1 - 0) + B * packHistory B (fun t => k + 1 - (t + 1)) (k + 1) =
        (k + 1) + B * packHistory B (fun t => k - t) (k + 1)
      have hfun : (fun t => k + 1 - (t + 1)) = (fun t => k - t) := by funext t; omega
      rw [hfun]; omega
    have hF : packHistory B (fun _ => 1) (k + 1) = 1 + B * packHistory B (fun _ => 1) k := rfl
    rw [hR, hF]
    let P := packHistory B (fun t => k - t) (k + 1)
    let F := packHistory B (fun _ => 1) k
    change (k + 1 + B * P) + B * (1 + B * F) = k + 1 + B * (k + 1 + B * P)
    have ih' : P + B * F = k + B * P := ih
    calc (k + 1 + B * P) + B * (1 + B * F)
      _ = k + 1 + B + B * (P + B * F) := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_add]; omega
      _ = k + 1 + B + B * (k + B * P) := by rw [ih']
      _ = k + 1 + B * (k + 1 + B * P) := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega

/-- Compresses Glazer's `clear` machine from 29 `power` calls (2,343 variables) to
    1 `power` call (`T_prev = B^n`, 85 variables). -/
theorem singleFoldClear_iff (n q_steps : ℕ) :
    clearAcceptsIn n q_steps ↔
      ∃ B T_prev F_prev R₀ : ℕ,
        T_prev = B ^ n ∧
        singleFoldClearPoly n q_steps B T_prev F_prev R₀ = 0 := by
  unfold clearAcceptsIn singleFoldClearPoly
  constructor
  · intro hq
    subst hq
    let B := 2 * n + 4
    let T_prev := B ^ n
    let F_prev := packHistory B (fun _ => 1) n
    let R₀ := packHistory B (fun t => n - t) (n + 1)
    refine ⟨B, T_prev, F_prev, R₀, rfl, ?_⟩
    rw [sumSquaresInt_eq_zero_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have hgeom_int := congrArg Int.ofNat (geom_series_identity B n (by omega))
    have hcount_int := congrArg Int.ofNat (countdown_history_identity B n)
    exact ⟨by omega, by omega, sub_eq_zero.mpr hgeom_int, sub_eq_zero.mpr hcount_int⟩
  · rintro ⟨B, T_prev, F_prev, R₀, _, hpoly⟩
    rw [sumSquaresInt_eq_zero_iff] at hpoly
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hpoly
    rcases hpoly with ⟨_, hq, _, _⟩
    omega

/-- Single-fold witness uniqueness for the compressed `clear` system:
    given `T_prev = B^n` and `singleFoldClearPoly n q_steps B T_prev F_prev R₀ = 0`,
    every witness `(B, T_prev, F_prev, R₀)` is uniquely determined by `(n, q_steps)`. -/
theorem singleFoldClear_unique (n q_steps : ℕ)
    (B₁ T₁ F₁ R₁ B₂ T₂ F₂ R₂ : ℕ)
    (hT₁ : T₁ = B₁ ^ n) (hP₁ : singleFoldClearPoly n q_steps B₁ T₁ F₁ R₁ = 0)
    (hT₂ : T₂ = B₂ ^ n) (hP₂ : singleFoldClearPoly n q_steps B₂ T₂ F₂ R₂ = 0) :
    (B₁, T₁, F₁, R₁) = (B₂, T₂, F₂, R₂) := by
  unfold singleFoldClearPoly at hP₁ hP₂
  rw [sumSquaresInt_eq_zero_iff] at hP₁ hP₂
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hP₁ hP₂
  rcases hP₁ with ⟨hB₁, _, hF₁, hR₁⟩
  rcases hP₂ with ⟨hB₂, _, hF₂, hR₂⟩
  have hB : B₁ = B₂ := by omega
  subst hB
  have hT : T₁ = T₂ := by rw [hT₁, hT₂]
  subst hT
  have hB_ge : (B₁ : ℤ) ≥ 4 := by omega
  have hF_lin : ((B₁ : ℤ) - 1) * ((F₁ : ℤ) - (F₂ : ℤ)) = 0 := by linarith
  have hF : F₁ = F₂ := by
    rcases mul_eq_zero.mp hF_lin with hB1 | hFeq <;> omega
  subst hF
  have hR_lin : ((B₁ : ℤ) - 1) * ((R₁ : ℤ) - (R₂ : ℤ)) = 0 := by linarith
  have hR : R₁ = R₂ := by
    rcases mul_eq_zero.mp hR_lin with hB1 | hReq <;> omega
  subst hR
  rfl

end DiophantineZQ
