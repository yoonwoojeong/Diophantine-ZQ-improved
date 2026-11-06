/-
  DiophantineZQ.Domains
  =====================
  Mathlib-backed Diophantine and Single-Fold representations over `ℕ`, `ℤ`, and `ℚ`:
  1. Single-Fold Diophantine representations (`evalNat`, `Represents`) on
     `MvPolynomial (Fin n ⊕ Fin m) ℤ` following `OAI.SingleFold` (`openai/math`).
  2. Rational Diophantine formulas, sum-of-squares conjunction (`conjoin`),
     product disjunction (`disjoin`), fresh witness-block renaming (`leftVars`, `rightVars`),
     and denominator clearing (`commonDenominator`, `exists_integer_equation`) over
     `MvPolynomial (Fin n) ℚ` and `MvPolynomial (Fin n) ℤ`.
  3. Integer vs. rational witness separation (`int_vs_rat_witness_separation`) over
     genuine `MvPolynomial (Fin 1) ℤ`.
  4. Unreferenced ambient variables vs. genuine functional witness elimination.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace DiophantineZQ

/-! ## 1. Single-Fold and Existential Diophantine Representations (`MvPolynomial`) -/

/-- Evaluation over `ℤ` of an integer polynomial `P : MvPolynomial (Fin n ⊕ Fin m) ℤ`
    at natural parameters `a : Fin n → ℕ` and natural witnesses `w : Fin m → ℕ`
    (matching `OAI.SingleFold.evalNat` from `openai/math`). -/
def evalNat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Evaluation over `ℚ` of an integer polynomial `P : MvPolynomial (Fin n ⊕ Fin m) ℤ`
    at rational parameters `a : Fin n → ℚ` and rational witnesses `w : Fin m → ℚ`. -/
def evalRat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℚ) (w : Fin m → ℚ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) (Sum.elim a w) P

/-- Standard existential Diophantine representation over `ℕ`:
    `a ∈ S ↔ ∃ w : Fin m → ℕ, evalNat P a w = 0`. -/
def DiophantineRepresents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ S ↔ ∃ w, evalNat P a w = 0

/-- Single-fold Diophantine representation over `ℕ` (`OAI.SingleFold.Represents`):
    exact existence on members, no witness on nonmembers, and uniqueness of the
    entire witness tuple `w` on every input. -/
def SingleFoldRepresents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, (a ∈ S ↔ ∃ w, evalNat P a w = 0) ∧
    ∀ w v, evalNat P a w = 0 → evalNat P a v = 0 → w = v

theorem SingleFoldRepresents.toDiophantine {n m : ℕ}
    {P : MvPolynomial (Fin n ⊕ Fin m) ℤ} {S : Set (Fin n → ℕ)}
    (h : SingleFoldRepresents P S) : DiophantineRepresents P S :=
  fun a => (h a).1

/-! ## 2. Rational Polynomial Compilation & Denominator Clearing (`MvPolynomial (Fin n) ℚ`) -/

/-- Positive equational formulas whose atoms are rational multivariate polynomial equations. -/
inductive EquationFormula (n : ℕ) where
  | equation : MvPolynomial (Fin n) ℚ → EquationFormula n
  | verum : EquationFormula n
  | falsum : EquationFormula n
  | conj : EquationFormula n → EquationFormula n → EquationFormula n
  | disj : EquationFormula n → EquationFormula n → EquationFormula n

/-- Semantic satisfaction of an `EquationFormula` at a rational point `x : Fin n → ℚ`. -/
def holds {n : ℕ} (x : Fin n → ℚ) : EquationFormula n → Prop
  | .equation P => MvPolynomial.eval x P = 0
  | .verum => True
  | .falsum => False
  | .conj F G => holds x F ∧ holds x G
  | .disj F G => holds x F ∨ holds x G

/-- Recursive compiler mapping an `EquationFormula` to a single `MvPolynomial (Fin n) ℚ`. -/
def compile {n : ℕ} : EquationFormula n → MvPolynomial (Fin n) ℚ
  | .equation P => P
  | .verum => 0
  | .falsum => 1
  | .conj F G => compile F ^ 2 + compile G ^ 2
  | .disj F G => compile F * compile G

/-- Left witness-block variable embedding. -/
def leftVars {n m k : ℕ} :
    Fin n ⊕ Fin m → Fin n ⊕ (Fin m ⊕ Fin k)
  | .inl i => .inl i
  | .inr j => .inr (.inl j)

/-- Right witness-block variable embedding. -/
def rightVars {n m k : ℕ} :
    Fin n ⊕ Fin k → Fin n ⊕ (Fin m ⊕ Fin k)
  | .inl i => .inl i
  | .inr j => .inr (.inr j)

/-- Product of the denominators of all coefficients in the support of `P`. -/
def commonDenominator {n : ℕ} (P : MvPolynomial (Fin n) ℚ) : ℕ :=
  P.support.prod (fun d => (P.coeff d).den)

/-- `n`-ary conjunction of rational polynomials via sum of squares. -/
def conjoin {n : ℕ} (ps : List (MvPolynomial (Fin n) ℚ)) : MvPolynomial (Fin n) ℚ :=
  (ps.map (fun P => P ^ 2)).sum

/-- `n`-ary disjunction of rational polynomials via product. -/
def disjoin {n : ℕ} (ps : List (MvPolynomial (Fin n) ℚ)) : MvPolynomial (Fin n) ℚ :=
  ps.prod

theorem eval_conjoin_nonneg {n : ℕ}
    (ps : List (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ) :
    0 ≤ MvPolynomial.eval x (conjoin ps) := by
  induction ps with
  | nil => simp [conjoin]
  | cons P ps ih =>
    simp only [conjoin, List.map_cons, List.sum_cons, map_add, map_pow] at ih ⊢
    exact add_nonneg (sq_nonneg _) ih

theorem eval_conjoin_eq_zero_iff {n : ℕ}
    (ps : List (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ) :
    MvPolynomial.eval x (conjoin ps) = 0 ↔
      ∀ P ∈ ps, MvPolynomial.eval x P = 0 := by
  induction ps with
  | nil => simp [conjoin]
  | cons P ps ih =>
    have hnn := eval_conjoin_nonneg ps x
    simp only [conjoin, List.map_cons, List.sum_cons, map_add, map_pow] at ih hnn ⊢
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) hnn, pow_eq_zero_iff two_ne_zero, ih,
      List.forall_mem_cons]

theorem eval_disjoin_eq_zero_iff {n : ℕ}
    (ps : List (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ) :
    MvPolynomial.eval x (disjoin ps) = 0 ↔
      ∃ P ∈ ps, MvPolynomial.eval x P = 0 := by
  induction ps with
  | nil => simp [disjoin]
  | cons P ps ih =>
    simp only [disjoin, List.prod_cons, map_mul] at ih ⊢
    rw [mul_eq_zero, ih]
    constructor
    · rintro (h | ⟨Q, hQ, h⟩)
      · exact ⟨P, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨Q, List.mem_cons.mpr (Or.inr hQ), h⟩
    · rintro ⟨Q, hQ, h⟩
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact Or.inl h
      · exact Or.inr ⟨Q, hQ, h⟩

theorem eval_compile_eq_zero_iff {n : ℕ}
    (F : EquationFormula n) (x : Fin n → ℚ) :
    MvPolynomial.eval x (compile F) = 0 ↔ holds x F := by
  induction F with
  | equation P => simp [compile, holds]
  | verum => simp [compile, holds]
  | falsum => simp [compile, holds]
  | conj F G ihF ihG =>
    simp only [compile, holds, map_add, map_pow]
    rw [sq_add_sq_eq_zero, ihF, ihG]
  | disj F G ihF ihG =>
    simp only [compile, holds, map_mul]
    rw [mul_eq_zero, ihF, ihG]

theorem sum_elim_comp_leftVars {n m k : ℕ} (x : Fin n → ℚ)
    (yz : Fin m ⊕ Fin k → ℚ) :
    Sum.elim x yz ∘ leftVars (n := n) (m := m) (k := k) = Sum.elim x (yz ∘ Sum.inl) := by
  funext i
  cases i <;> rfl

theorem sum_elim_comp_rightVars {n m k : ℕ} (x : Fin n → ℚ)
    (yz : Fin m ⊕ Fin k → ℚ) :
    Sum.elim x yz ∘ rightVars (n := n) (m := m) (k := k) = Sum.elim x (yz ∘ Sum.inr) := by
  funext i
  cases i <;> rfl

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
     (∃ z : Fin k → ℚ, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by
  simp only [map_add, map_pow, MvPolynomial.eval_rename, sum_elim_comp_leftVars,
    sum_elim_comp_rightVars, sq_add_sq_eq_zero]
  constructor
  · rintro ⟨yz, hP, hQ⟩
    exact ⟨⟨yz ∘ Sum.inl, hP⟩, ⟨yz ∘ Sum.inr, hQ⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨Sum.elim y z, ?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact hy
    · rw [Sum.elim_comp_inr]; exact hz

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
     (∃ z : Fin k → ℚ, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by
  simp only [map_mul, MvPolynomial.eval_rename, sum_elim_comp_leftVars,
    sum_elim_comp_rightVars, mul_eq_zero]
  constructor
  · rintro ⟨yz, hP | hQ⟩
    · exact Or.inl ⟨yz ∘ Sum.inl, hP⟩
    · exact Or.inr ⟨yz ∘ Sum.inr, hQ⟩
  · rintro (⟨y, hy⟩ | ⟨z, hz⟩)
    · refine ⟨Sum.elim y (fun _ => 0), Or.inl ?_⟩
      rw [Sum.elim_comp_inl]; exact hy
    · refine ⟨Sum.elim (fun _ => 0) z, Or.inr ?_⟩
      rw [Sum.elim_comp_inr]; exact hz

theorem commonDenominator_pos {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    0 < commonDenominator P := by
  unfold commonDenominator
  exact Finset.prod_induction _ (fun d => 0 < d) (fun _ _ ha hb => Nat.mul_pos ha hb)
    Nat.one_pos (fun d _ => (P.coeff d).den_pos)

theorem exists_int_eq_commonDenominator_mul_coeff {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) (d : Fin n →₀ ℕ) :
    ∃ z : ℤ, (z : ℚ) = (commonDenominator P : ℚ) * P.coeff d := by
  by_cases hd : d ∈ P.support
  · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun d => (P.coeff d).den) hd
    have hcd : commonDenominator P = (P.coeff d).den * e := he
    refine ⟨(e : ℤ) * (P.coeff d).num, ?_⟩
    rw [hcd, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, mul_comm ((P.coeff d).den : ℚ),
      mul_assoc, Rat.den_mul_eq_num]
  · refine ⟨0, ?_⟩
    rw [MvPolynomial.notMem_support_iff.mp hd, mul_zero, Int.cast_zero]

theorem exists_integer_multiple {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) Q =
        MvPolynomial.C (commonDenominator P : ℚ) * P := by
  have h : MvPolynomial.C (commonDenominator P : ℚ) * P ∈
      Set.range (MvPolynomial.map (σ := Fin n) (Int.castRingHom ℚ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    rw [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨d, -, rfl⟩ := hc
    obtain ⟨z, hz⟩ := exists_int_eq_commonDenominator_mul_coeff P d
    exact ⟨z, by rw [MvPolynomial.coeff_C_mul, ← hz, Int.coe_castRingHom]⟩
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, hQ⟩

theorem exists_integer_equation {n : ℕ} (F : EquationFormula n) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      ∀ x : Fin n → ℚ,
        (MvPolynomial.eval₂ (Int.castRingHom ℚ) x Q = 0 ↔ holds x F) := by
  obtain ⟨Q, hQ⟩ := exists_integer_multiple (compile F)
  have hne : (commonDenominator (compile F) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (commonDenominator_pos (compile F)).ne'
  refine ⟨Q, fun x => ?_⟩
  rw [← MvPolynomial.eval_map, hQ, map_mul, MvPolynomial.eval_C, mul_eq_zero,
    eval_compile_eq_zero_iff]
  exact or_iff_right hne

/-! ## 3. Sum-of-Squares Conjunction over `ℤ` & Integer vs. Rational Witness Separation -/

/-- Sum of squares of a list of integers, used to bundle concrete polynomial residuals. -/
def sumSquaresInt : List ℤ → ℤ
  | [] => 0
  | x :: xs => x ^ 2 + sumSquaresInt xs

theorem sumSquaresInt_nonneg : ∀ xs : List ℤ, 0 ≤ sumSquaresInt xs
  | [] => le_refl 0
  | x :: xs => add_nonneg (sq_nonneg x) (sumSquaresInt_nonneg xs)

theorem sumSquaresInt_eq_zero_iff :
    ∀ xs : List ℤ, sumSquaresInt xs = 0 ↔ ∀ x ∈ xs, x = 0
  | [] => by simp [sumSquaresInt]
  | x :: xs => by
    simp only [sumSquaresInt, List.mem_cons, forall_eq_or_imp]
    have hx := sq_nonneg x
    have hxs := sumSquaresInt_nonneg xs
    rw [add_eq_zero_iff_of_nonneg hx hxs, sq_eq_zero_iff, sumSquaresInt_eq_zero_iff xs]

/-- The linear polynomial `2 * X₀ - 1 ∈ ℤ[X₀]` has no root in `ℤ`,
    but has the unique rational root `1 / 2 ∈ ℚ`. -/
def twoMulSubOnePoly : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.C 2 * MvPolynomial.X 0 - MvPolynomial.C 1

theorem int_vs_rat_witness_separation :
    (¬ ∃ w : Fin 1 → ℤ, MvPolynomial.eval w twoMulSubOnePoly = 0) ∧
    (∃ q : Fin 1 → ℚ, MvPolynomial.eval₂ (Int.castRingHom ℚ) q twoMulSubOnePoly = 0) := by
  unfold twoMulSubOnePoly
  constructor
  · rintro ⟨w, hw⟩
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at hw
    omega
  · refine ⟨fun _ => (1 : ℚ) / 2, ?_⟩
    rw [← MvPolynomial.eval_map]
    simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Int.coe_castRingHom]
    norm_num

/-! ## 4. Unreferenced Ambient Variables vs. Functional Witness Elimination -/

/-- A polynomial `P : MvPolynomial (Fin n ⊕ (Fin m ⊕ Fin k)) R` has an unreferenced
    tail of `k` witness variables if it lies in the image of `MvPolynomial.rename leftVars`. -/
def HasUnreferencedTail {n m k : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin n ⊕ (Fin m ⊕ Fin k)) R) : Prop :=
  ∃ P₀ : MvPolynomial (Fin n ⊕ Fin m) R,
    P = MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P₀

/-- Evaluating a polynomial with an unreferenced tail of `k` variables is independent of
    the `Fin k` witness assignment. -/
theorem eval_hasUnreferencedTail_indep {n m k : ℕ}
    {P : MvPolynomial (Fin n ⊕ (Fin m ⊕ Fin k)) ℤ}
    {P₀ : MvPolynomial (Fin n ⊕ Fin m) ℤ}
    (hP : P = MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P₀)
    (a : Fin n → ℤ) (w : Fin m → ℤ) (u₁ u₂ : Fin k → ℤ) :
    MvPolynomial.eval (Sum.elim a (Sum.elim w u₁)) P =
      MvPolynomial.eval (Sum.elim a (Sum.elim w u₂)) P := by
  subst hP
  simp only [MvPolynomial.eval_rename]
  have hfun : (Sum.elim a (Sum.elim w u₁) ∘ leftVars (n := n) (m := m) (k := k)) =
      (Sum.elim a (Sum.elim w u₂) ∘ leftVars (n := n) (m := m) (k := k)) := by
    funext x
    cases x <;> rfl
  rw [hfun]

/-- Genuine functional witness elimination over `ℤ` (`y = f a x`). -/
theorem functional_witness_elimination_int {α : Type*}
    (R : α → ℤ → ℤ → Prop) (f : α → ℤ → ℤ) :
    ∀ a : α, (∃ x y : ℤ, y = f a x ∧ R a x y) ↔ (∃ x : ℤ, R a x (f a x)) := by
  intro a
  exact ⟨by rintro ⟨x, _, rfl, hR⟩; exact ⟨x, hR⟩,
         by rintro ⟨x, hR⟩; exact ⟨x, f a x, rfl, hR⟩⟩

/-- Genuine functional subtraction elimination over `ℕ` (`w = s - v`) when `P` forces `v ≤ s`. -/
theorem functional_sub_elimination_nat
    (P : ℕ → ℕ → ℕ → Prop)
    (h_le : ∀ s v : ℕ, P s v (s - v) → v ≤ s) :
    ∀ s : ℕ, (∃ v w : ℕ, s = v + w ∧ P s v w) ↔ (∃ v : ℕ, P s v (s - v)) := by
  intro s
  constructor
  · rintro ⟨v, w, hsum, hP⟩
    have hw : w = s - v := by omega
    subst hw
    exact ⟨v, hP⟩
  · rintro ⟨v, hP⟩
    have hv : v ≤ s := h_le s v hP
    exact ⟨v, s - v, by omega, hP⟩

end DiophantineZQ
