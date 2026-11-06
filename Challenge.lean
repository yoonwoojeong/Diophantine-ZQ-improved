/-
  Challenge.lean
  ==============
  Self-contained specification module for `lake comparator` verification of
  `DiophantineZQ` against `Mathlib`.
  Every public definition matches `DiophantineZQ` byte-for-byte, and every
  target theorem is stated with `sorry`.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

noncomputable section

namespace DiophantineZQ

/-! ## 1. Domains (`DiophantineZQ.Domains`) -/

def evalNat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

def evalRat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℚ) (w : Fin m → ℚ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) (Sum.elim a w) P

def DiophantineRepresents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ S ↔ ∃ w, evalNat P a w = 0

def SingleFoldRepresents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, (a ∈ S ↔ ∃ w, evalNat P a w = 0) ∧
    ∀ w v, evalNat P a w = 0 → evalNat P a v = 0 → w = v

theorem SingleFoldRepresents.toDiophantine {n m : ℕ}
    {P : MvPolynomial (Fin n ⊕ Fin m) ℤ} {S : Set (Fin n → ℕ)}
    (h : SingleFoldRepresents P S) : DiophantineRepresents P S := by sorry

inductive EquationFormula (n : ℕ) where
  | equation : MvPolynomial (Fin n) ℚ → EquationFormula n
  | verum : EquationFormula n
  | falsum : EquationFormula n
  | conj : EquationFormula n → EquationFormula n → EquationFormula n
  | disj : EquationFormula n → EquationFormula n → EquationFormula n

def holds {n : ℕ} (x : Fin n → ℚ) : EquationFormula n → Prop
  | .equation P => MvPolynomial.eval x P = 0
  | .verum => True
  | .falsum => False
  | .conj F G => holds x F ∧ holds x G
  | .disj F G => holds x F ∨ holds x G

def compile {n : ℕ} : EquationFormula n → MvPolynomial (Fin n) ℚ
  | .equation P => P
  | .verum => 0
  | .falsum => 1
  | .conj F G => compile F ^ 2 + compile G ^ 2
  | .disj F G => compile F * compile G

def leftVars {n m k : ℕ} :
    Fin n ⊕ Fin m → Fin n ⊕ (Fin m ⊕ Fin k)
  | .inl i => .inl i
  | .inr j => .inr (.inl j)

def rightVars {n m k : ℕ} :
    Fin n ⊕ Fin k → Fin n ⊕ (Fin m ⊕ Fin k)
  | .inl i => .inl i
  | .inr j => .inr (.inr j)

def commonDenominator {n : ℕ} (P : MvPolynomial (Fin n) ℚ) : ℕ :=
  P.support.prod (fun d => (P.coeff d).den)

def conjoin {n : ℕ} (ps : List (MvPolynomial (Fin n) ℚ)) : MvPolynomial (Fin n) ℚ :=
  (ps.map (fun P => P ^ 2)).sum

def disjoin {n : ℕ} (ps : List (MvPolynomial (Fin n) ℚ)) : MvPolynomial (Fin n) ℚ :=
  ps.prod

theorem eval_conjoin_eq_zero_iff {n : ℕ}
    (ps : List (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ) :
    MvPolynomial.eval x (conjoin ps) = 0 ↔
      ∀ P ∈ ps, MvPolynomial.eval x P = 0 := by sorry

theorem eval_disjoin_eq_zero_iff {n : ℕ}
    (ps : List (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ) :
    MvPolynomial.eval x (disjoin ps) = 0 ↔
      ∃ P ∈ ps, MvPolynomial.eval x P = 0 := by sorry

theorem eval_compile_eq_zero_iff {n : ℕ}
    (F : EquationFormula n) (x : Fin n → ℚ) :
    MvPolynomial.eval x (compile F) = 0 ↔ holds x F := by sorry

theorem exists_conjunction_fresh_iff {n m k : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin m) ℚ)
    (Q : MvPolynomial (Fin n ⊕ Fin k) ℚ)
    (x : Fin n → ℚ) :
    (∃ yz : Fin m ⊕ Fin k → ℚ,
      MvPolynomial.eval (Sum.elim x yz)
        ((MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P) ^ 2 +
         (MvPolynomial.rename (rightVars (n := n) (m := m) (k := k)) Q) ^ 2) = 0)
    ↔
    ((∃ y : Fin m → ℚ, MvPolynomial.eval (Sum.elim x y) P = 0) ∧
     (∃ z : Fin k → ℚ, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by sorry

theorem exists_disjunction_fresh_iff {n m k : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin m) ℚ)
    (Q : MvPolynomial (Fin n ⊕ Fin k) ℚ)
    (x : Fin n → ℚ) :
    (∃ yz : Fin m ⊕ Fin k → ℚ,
      MvPolynomial.eval (Sum.elim x yz)
        (MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P *
         MvPolynomial.rename (rightVars (n := n) (m := m) (k := k)) Q) = 0)
    ↔
    ((∃ y : Fin m → ℚ, MvPolynomial.eval (Sum.elim x y) P = 0) ∨
     (∃ z : Fin k → ℚ, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by sorry

theorem commonDenominator_pos {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    0 < commonDenominator P := by sorry

theorem exists_integer_multiple {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) Q =
        MvPolynomial.C (commonDenominator P : ℚ) * P := by sorry

theorem exists_integer_equation {n : ℕ} (F : EquationFormula n) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      ∀ x : Fin n → ℚ,
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x Q = 0 ↔ holds x F) := by sorry

def sumSquaresInt : List ℤ → ℤ
  | [] => 0
  | x :: xs => x ^ 2 + sumSquaresInt xs

theorem sumSquaresInt_eq_zero_iff :
    ∀ xs : List ℤ, sumSquaresInt xs = 0 ↔ ∀ x ∈ xs, x = 0 := by sorry

def twoMulSubOnePoly : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.C 2 * MvPolynomial.X 0 - MvPolynomial.C 1

theorem int_vs_rat_witness_separation :
    (¬ ∃ w : Fin 1 → ℤ, MvPolynomial.eval w twoMulSubOnePoly = 0) ∧
    (∃ q : Fin 1 → ℚ, MvPolynomial.eval₂ (Int.castRingHom ℚ) q twoMulSubOnePoly = 0) := by sorry

def HasUnreferencedTail {n m k : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin n ⊕ (Fin m ⊕ Fin k)) R) : Prop :=
  ∃ P₀ : MvPolynomial (Fin n ⊕ Fin m) R,
    P = MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P₀

theorem eval_hasUnreferencedTail_indep {n m k : ℕ}
    {P : MvPolynomial (Fin n ⊕ (Fin m ⊕ Fin k)) ℤ}
    {P₀ : MvPolynomial (Fin n ⊕ Fin m) ℤ}
    (hP : P = MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P₀)
    (a : Fin n → ℤ) (w : Fin m → ℤ) (u₁ u₂ : Fin k → ℤ) :
    MvPolynomial.eval (Sum.elim a (Sum.elim w u₁)) P =
      MvPolynomial.eval (Sum.elim a (Sum.elim w u₂)) P := by sorry

theorem functional_witness_elimination_int {α : Type*}
    (R : α → ℤ → ℤ → Prop) (f : α → ℤ → ℤ) :
    ∀ a : α, (∃ x y : ℤ, y = f a x ∧ R a x y) ↔ (∃ x : ℤ, R a x (f a x)) := by sorry

theorem functional_sub_elimination_nat
    (P : ℕ → ℕ → ℕ → Prop)
    (h_le : ∀ s v : ℕ, P s v (s - v) → v ≤ s) :
    ∀ s : ℕ, (∃ v w : ℕ, s = v + w ∧ P s v w) ↔ (∃ v : ℕ, P s v (s - v)) := by sorry

/-! ## 2. SingleFold (`DiophantineZQ.SingleFold`) -/

def odd_witness (x : ℕ) : Prop := ∃ half : ℕ, x = 2 * half + 1

def mask (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose b a ∧ odd_witness c

def orthogonal (a b : ℕ) : Prop :=
  ∃ c : ℕ, c = Nat.choose (a + b) a ∧ odd_witness c

def bit_and (z x y : ℕ) : Prop :=
  ∃ a b : ℕ,
    x = z + a ∧ y = z + b ∧
    orthogonal z a ∧ orthogonal z b ∧ orthogonal a b

theorem choose_odd_iff_land_eq (a b : ℕ) :
    Odd (Nat.choose b a) ↔ a &&& b = a := by sorry

theorem choose_add_odd_iff_land_eq_zero (a b : ℕ) :
    Odd (Nat.choose (a + b) a) ↔ a &&& b = 0 := by sorry

theorem mask_iff_land_eq (a b : ℕ) :
    mask a b ↔ a &&& b = a := by sorry

theorem orthogonal_iff_land_eq_zero (a b : ℕ) :
    orthogonal a b ↔ a &&& b = 0 := by sorry

theorem bit_and_iff_land_eq (z x y : ℕ) :
    bit_and z x y ↔ z = x &&& y := by sorry

def IsDyadicHalfBase (L e : ℕ) : Prop :=
  2 ^ e ≤ L ∧ L < 2 ^ (e + 1)

theorem dyadic_exponent_unique (L e₁ e₂ : ℕ)
    (h₁ : IsDyadicHalfBase L e₁) (h₂ : IsDyadicHalfBase L e₂) : e₁ = e₂ := by sorry

theorem dyadic_exponent_exists (L : ℕ) (hL : 0 < L) :
    ∃ e : ℕ, IsDyadicHalfBase L e := by sorry

def packHistory (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f 0 + B * packHistory B (fun t => f (t + 1)) n

theorem packHistory_eq_finset_sum (B : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    packHistory B f n = ∑ t ∈ Finset.range n, f t * B ^ t := by sorry

theorem packed_register_decode {B K q init : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t, t ≤ q → ρ t < K) (hα : ∀ t, t ≤ q → α t ≤ 1)
    (hγ : ∀ t, t ≤ q → γ t ≤ 1) (hinit : init < K)
    (heq : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t) + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t)
         = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
                + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t)) :
    ρ 0 = init ∧ (∀ t, t < q → ρ (t+1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by sorry

theorem packHistory_eq_iff (B : ℕ) (f g : ℕ → ℕ) (n : ℕ)
    (hf : ∀ t, t < n → f t < B) (hg : ∀ t, t < n → g t < B) :
    packHistory B f n = packHistory B g n ↔ ∀ t, t < n → f t = g t := by sorry

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
       ρ_last = ρ q) := by sorry

theorem complement_mask_slot_zero_test (w r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t) :
    let v_t := 1 - z_t
    r_t &&& ((2 ^ w - 1) * v_t) = r_t ↔ (z_t = 1 → r_t = 0) := by sorry

theorem complement_mask_iff_zero_test (w r_t z_t : ℕ)
    (hz : z_t = 0 ∨ z_t = 1)
    (hr_mask : mask r_t (2 ^ w - 1)) :
    mask r_t ((2 ^ w - 1) * (1 - z_t)) ↔ (z_t = 1 → r_t = 0) := by sorry

theorem single_fold_branch_correct (w r_t r_next s_t v_t z_t : ℕ)
    (_hs : s_t = 0 ∨ s_t = 1) (_hv : v_t = 0 ∨ v_t = 1) (hz : z_t = 0 ∨ z_t = 1)
    (hpart : s_t = v_t + z_t)
    (hr_mask : r_t &&& (2 ^ w - 1) = r_t)
    (hzero_guard : r_t &&& ((2 ^ w - 1) * (1 - z_t)) = r_t)
    (hstep : r_next + v_t = r_t) :
    (s_t = 0 → v_t = 0 ∧ z_t = 0 ∧ r_next = r_t) ∧
    (s_t = 1 ∧ r_t = 0 → v_t = 0 ∧ z_t = 1 ∧ r_next = 0) ∧
    (s_t = 1 ∧ 0 < r_t → v_t = 1 ∧ z_t = 0 ∧ r_next = r_t - 1) := by sorry

theorem disjoint_in_D_mask_iff (c r z : ℕ) (hz : z = 0 ∨ z = 1) :
    mask (r + (2 ^ c - 1) * z) (2 ^ c - 1) ↔
      (mask r (2 ^ c - 1) ∧ (z = 1 → r = 0)) := by sorry

/-! ## 3. SmallTM (`DiophantineZQ.SmallTM`) -/

inductive Dir where
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

inductive Action (numStates : ℕ) where
  | halt : Action numStates
  | step (writeBit : ℕ) (dir : Dir) (nextState : Fin numStates) : Action numStates
  deriving DecidableEq, Repr

def Machine (numStates : ℕ) := Fin numStates → Bool → Action numStates

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

def isBitPoly (b : ℕ) : ℤ :=
  (b : ℤ) * ((b : ℤ) - 1)

def bitSplitResidual (X x_half bit : ℕ) : ℤ :=
  sumSquaresInt [
    isBitPoly bit,
    (X : ℤ) - (2 * (x_half : ℤ) + (bit : ℤ))
  ]

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
    stepTM BB2 c = some c' := by sorry

theorem bb2StepPoly_unique (c c' : TMConfig)
    (rh₁ rb₁ lh₁ lb₁ rh₂ rb₂ lh₂ lb₂ : ℕ)
    (h₁ : bb2StepPoly c c' rh₁ rb₁ lh₁ lb₁ = 0)
    (h₂ : bb2StepPoly c c' rh₂ rb₂ lh₂ lb₂ = 0) :
    (rh₁, rb₁, lh₁, lb₁) = (rh₂, rb₂, lh₂, lb₂) := by sorry

theorem bb2_halts_in_6 : HaltsIn BB2 initConfig 6 := by sorry

theorem bb2_halts : Halts BB2 := by sorry

def clearAcceptsIn (n q_steps : ℕ) : Prop :=
  q_steps = n + 1

def singleFoldClearPoly (n q_steps B T_prev F_prev R₀ : ℕ) : ℤ :=
  sumSquaresInt [
    (B : ℤ) - (2 * (n : ℤ) + 4),
    (q_steps : ℤ) - ((n : ℤ) + 1),
    (B : ℤ) * (F_prev : ℤ) + 1 - ((T_prev : ℤ) + (F_prev : ℤ)),
    (R₀ : ℤ) + (B : ℤ) * (F_prev : ℤ) - ((n : ℤ) + (B : ℤ) * (R₀ : ℤ))
  ]

theorem singleFoldClear_iff (n q_steps : ℕ) :
    clearAcceptsIn n q_steps ↔
      ∃ B T_prev F_prev R₀ : ℕ,
        T_prev = B ^ n ∧
        singleFoldClearPoly n q_steps B T_prev F_prev R₀ = 0 := by sorry

theorem singleFoldClear_unique (n q_steps : ℕ)
    (B₁ T₁ F₁ R₁ B₂ T₂ F₂ R₂ : ℕ)
    (hT₁ : T₁ = B₁ ^ n) (hP₁ : singleFoldClearPoly n q_steps B₁ T₁ F₁ R₁ = 0)
    (hT₂ : T₂ = B₂ ^ n) (hP₂ : singleFoldClearPoly n q_steps B₂ T₂ F₂ R₂ = 0) :
    (B₁, T₁, F₁, R₁) = (B₂, T₂, F₂, R₂) := by sorry

/-! ## 4. Antihydra (`DiophantineZQ.Antihydra`) -/

def AntihydraTM : Machine 6 := fun q s =>
  match q.val, s with
  | 0, false => .step 1 .R ⟨1, by decide⟩
  | 0, true  => .step 1 .R ⟨0, by decide⟩
  | 1, false => .step 0 .L ⟨2, by decide⟩
  | 1, true  => .step 1 .L ⟨4, by decide⟩
  | 2, false => .step 1 .L ⟨3, by decide⟩
  | 2, true  => .step 1 .L ⟨2, by decide⟩
  | 3, false => .step 1 .L ⟨0, by decide⟩
  | 3, true  => .step 0 .L ⟨1, by decide⟩
  | 4, false => .step 1 .L ⟨5, by decide⟩
  | 4, true  => .step 1 .R ⟨4, by decide⟩
  | _, false => .halt
  | _, true  => .step 0 .R ⟨0, by decide⟩

theorem antihydra_reaches_start_in_12_steps :
    runTM AntihydraTM 12 initConfig = some ⟨5, 7, 3⟩ := by sorry

structure AHState where
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq, Repr

def ahStart : AHState := ⟨0, 3, 1⟩

def antihydraNext (s : AHState) : Option AHState :=
  match s.a, s.b, s.c with
  | 0, 0, c => some ⟨0, c + 3, 1⟩
  | a + 1, 0, c => some ⟨0, a + c + 7, 1⟩
  | a, 1, c => some ⟨a + 2, c + 3, 1⟩
  | 0, 2, _ => none
  | a + 1, 2, c => some ⟨a, c + 4, 1⟩
  | a, b + 3, c => some ⟨a, b + 1, c + 3⟩

def runAntihydraAccel : ℕ → AHState → Option AHState
  | 0, s => some s
  | n + 1, s =>
      match antihydraNext s with
      | none => none
      | some s' => runAntihydraAccel n s'

def AntihydraCollatzHaltsIn (n : ℕ) : Prop :=
  ∃ s_f : AHState, runAntihydraAccel n ahStart = some s_f ∧ antihydraNext s_f = none

def AntihydraCollatzHalts : Prop :=
  ∃ n : ℕ, AntihydraCollatzHaltsIn n

def antihydraHaltPoly (s : AHState) : ℤ :=
  sumSquaresInt [(s.a : ℤ) - 0, (s.b : ℤ) - 2]

def antihydraStepPoly (s s' : AHState) (d : ℕ) : ℤ :=
  let br1 := sumSquaresInt [
    (s.a : ℤ) - 0, (s.b : ℤ) - 0, (d : ℤ) - 0,
    (s'.a : ℤ) - 0, (s'.b : ℤ) - ((s.c : ℤ) + 3), (s'.c : ℤ) - 1
  ]
  let br2 := sumSquaresInt [
    (s.a : ℤ) - ((d : ℤ) + 1), (s.b : ℤ) - 0,
    (s'.a : ℤ) - 0, (s'.b : ℤ) - ((d : ℤ) + (s.c : ℤ) + 7), (s'.c : ℤ) - 1
  ]
  let br3 := sumSquaresInt [
    (s.b : ℤ) - 1, (d : ℤ) - 0,
    (s'.a : ℤ) - ((s.a : ℤ) + 2), (s'.b : ℤ) - ((s.c : ℤ) + 3), (s'.c : ℤ) - 1
  ]
  let br4 := sumSquaresInt [
    (s.a : ℤ) - ((d : ℤ) + 1), (s.b : ℤ) - 2,
    (s'.a : ℤ) - (d : ℤ), (s'.b : ℤ) - ((s.c : ℤ) + 4), (s'.c : ℤ) - 1
  ]
  let br5 := sumSquaresInt [
    (s.b : ℤ) - ((d : ℤ) + 3),
    (s'.a : ℤ) - (s.a : ℤ), (s'.b : ℤ) - ((d : ℤ) + 1), (s'.c : ℤ) - ((s.c : ℤ) + 3)
  ]
  br1 * br2 * br3 * br4 * br5

theorem antihydraStepPoly_iff_next (s s' : AHState) :
    (∃ d : ℕ, antihydraStepPoly s s' d = 0) ↔
    antihydraNext s = some s' := by sorry

theorem antihydraStepPoly_unique (s s' : AHState) (d₁ d₂ : ℕ)
    (h₁ : antihydraStepPoly s s' d₁ = 0)
    (h₂ : antihydraStepPoly s s' d₂ = 0) :
    d₁ = d₂ := by sorry

def antihydraStepsResidual : ℕ → (ℕ → AHState) → (ℕ → ℕ) → ℤ
  | 0, _, _ => 0
  | n + 1, traj, d_seq =>
      sumSquaresInt [
        antihydraStepPoly (traj 0) (traj 1) (d_seq 0),
        antihydraStepsResidual n (fun t => traj (t + 1)) (fun t => d_seq (t + 1))
      ]

def antihydraTrajectoryPoly (n : ℕ) (traj : ℕ → AHState) (d_seq : ℕ → ℕ) : ℤ :=
  sumSquaresInt [
    ((traj 0).a : ℤ) - 0, ((traj 0).b : ℤ) - 3, ((traj 0).c : ℤ) - 1,
    antihydraStepsResidual n traj d_seq,
    antihydraHaltPoly (traj n)
  ]

theorem antihydra_halts_iff_diophantine :
    AntihydraCollatzHalts ↔
      ∃ (n : ℕ) (traj : ℕ → AHState) (d_seq : ℕ → ℕ),
        antihydraTrajectoryPoly n traj d_seq = 0 := by sorry

/-! ## 5. ReductionAnalysis (`DiophantineZQ.ReductionAnalysis`) -/

theorem disjoint_in_D_slot_zero_test (K r z : ℕ) (_hK : 1 ≤ K)
    (hr : r ≤ K - 1) (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (z = 1 → r = 0) := by sorry

theorem combined_bound_and_zero_test_in_D (K r z : ℕ) (_hK : 1 ≤ K)
    (hz : z = 0 ∨ z = 1) :
    r + (K - 1) * z ≤ K - 1 ↔ (r ≤ K - 1 ∧ (z = 1 → r = 0)) := by sorry

theorem power_positive_base_iff (P Q E : ℕ) (hQ : 1 ≤ Q) :
    ((E = 0 ∧ P = 1) ∨ (Q = 0 ∧ 1 ≤ E ∧ P = 0) ∨ (1 ≤ Q ∧ 1 ≤ E ∧ P = Q ^ E)) ↔
    ((E = 0 ∧ P = 1) ∨ (1 ≤ E ∧ P = Q ^ E)) := by sorry

def unsharedMaskPowerCalls (M : ℕ) : ℕ := 3 * M
def sharedMaskPowerCalls (M : ℕ) : ℕ := 2 + M

theorem shared_mask_power_savings (M : ℕ) (hM : 1 ≤ M) :
    unsharedMaskPowerCalls M - sharedMaskPowerCalls M = 2 * (M - 1) := by sorry

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

theorem glazer_baseline_powers_param_eq : baselinePowerCalls glazerRM = 15845 := by sorry
theorem glazer_stage1_powers_param_eq : stage1PowerCallsParam glazerRM = 8489 := by sorry
theorem glazer_stage2_powers_param_eq : stage2PowerCallsParam glazerRM = 2631 := by sorry

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

def precisionRatWitnesses (explicitWitnesses numConstants numAdds numMuls numPowers perPowerWitnesses : ℕ) : ℕ :=
  3 + explicitWitnesses * 5
    + (5 + explicitWitnesses) * naturalGuardWitnesses
    + numConstants * 6
    + numAdds * (5 + rawAddWitnesses)
    + numMuls * (5 + multiplyWitnesses)
    + numPowers * (5 + perPowerWitnesses)

theorem glazer_total_rat_witnesses_eq :
    nonPrecisionRatWitnesses + precisionRatWitnesses 54051 4 125327 98382 15845 powerValueWitnesses
    = 292890231904 := by sorry

theorem glazer_total_nat_vars_eq :
    5 + 54051 + 15845 * 79 = 1305811 := by sorry

def stage1NatVars : ℕ := 5 + 29731 + 8489 * 79
def stage1RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses + precisionRatWitnesses 29731 4 70565 54282 8489 powerValueWitnesses

theorem stage1_nat_vars_eq : stage1NatVars = 700367 := by sorry
theorem stage1_rat_witnesses_eq : stage1RatWitnesses = 157081401474 := by sorry

def stage2PowerCalls : ℕ := 2 + (2 + 2421) + (2 + 204)
def stage2ExplicitWitnesses : ℕ := 15971
def stage2NatVars : ℕ := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 79
def stage2RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls powerValueWitnesses

theorem stage2_power_calls_eq : stage2PowerCalls = 2631 := by sorry
theorem stage2_nat_vars_eq : stage2NatVars = 223825 := by sorry
theorem stage2_rat_witnesses_eq : stage2RatWitnesses = 50103122522 := by sorry

def positiveBasePowerValueWitnesses : ℕ :=
  3 + 77 * 5 + 77 * naturalGuardWitnesses + 3 * 6 + 192 * (5 + rawAddWitnesses) + 186 * (5 + multiplyWitnesses)

def stage3NatVars : ℕ := 5 + stage2ExplicitWitnesses + stage2PowerCalls * 77
def stage3RatWitnesses : ℕ :=
  nonPrecisionRatWitnesses
    + precisionRatWitnesses stage2ExplicitWitnesses 4 41855 30130 stage2PowerCalls positiveBasePowerValueWitnesses

theorem stage3_nat_vars_eq : stage3NatVars = 218563 := by sorry
theorem stage3_rat_witnesses_eq : stage3RatWitnesses = 48993319364 := by sorry
theorem stage3_rat_savings_eq :
    292890231904 - stage3RatWitnesses = 243896912540 := by sorry

end DiophantineZQ
