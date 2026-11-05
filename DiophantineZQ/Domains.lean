/-
  DiophantineZQ.Domains
  =====================
  Explicit domain-typed Diophantine representations over ℕ, ℤ, and ℚ,
  sum-of-squares conjunction, product disjunction, integer-vs-rational
  witness separation, and unreferenced ambient variables vs. genuine
  functional witness elimination.
-/

namespace DiophantineZQ

/-! ## 1. Domain-Typed Diophantine Predicates -/

/-- A predicate `S : α → Prop` is Diophantine over `ℕ` with `m` natural witnesses. -/
def IsNatDiophantine {α : Type} (S : α → Prop) (m : Nat)
    (P : α → (Fin m → Nat) → Int) : Prop :=
  ∀ a : α, S a ↔ ∃ w : Fin m → Nat, P a w = 0

/-- A predicate `S : α → Prop` is Diophantine over `ℤ` with `m` integer witnesses. -/
def IsIntDiophantine {α : Type} (S : α → Prop) (m : Nat)
    (P : α → (Fin m → Int) → Int) : Prop :=
  ∀ a : α, S a ↔ ∃ z : Fin m → Int, P a z = 0

/-- Formal rational number `(num, den)` with `0 < den`. -/
structure QVal where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

namespace QVal

def EqRat (a b : QVal) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

def ofInt (z : Int) : QVal :=
  ⟨z, 1, Nat.one_pos⟩

def IsInteger (q : QVal) : Prop :=
  ∃ z : Int, q.num = z * (q.den : Int)

theorem ofInt_isInteger (z : Int) : IsInteger (ofInt z) :=
  ⟨z, by simp [ofInt]⟩

theorem isInteger_iff_eqRat_ofInt (q : QVal) :
    IsInteger q ↔ ∃ z : Int, EqRat q (ofInt z) := by
  simp [IsInteger, EqRat, ofInt]

end QVal

/-! ## 2. Sum-of-Squares Conjunction & Product Disjunction over ℤ -/

theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    rw [← Int.neg_mul_neg]
    exact Int.mul_nonneg h' h'

theorem sq_eq_zero_iff_int (x : Int) : x * x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  rcases Int.mul_eq_zero.mp h with hx | hx <;> exact hx

theorem sq_add_sq_eq_zero_iff_int (a b : Int) :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  have ha := sq_nonneg_int a
  have hb := sq_nonneg_int b
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  exact ⟨(sq_eq_zero_iff_int a).mp (by omega), (sq_eq_zero_iff_int b).mp (by omega)⟩

theorem mul_eq_zero_iff_int (a b : Int) :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  Int.mul_eq_zero

def sumSquaresInt : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSquaresInt xs

theorem sumSquaresInt_nonneg : ∀ xs : List Int, 0 ≤ sumSquaresInt xs
  | [] => Int.le_refl 0
  | x :: xs => Int.add_nonneg (sq_nonneg_int x) (sumSquaresInt_nonneg xs)

theorem sumSquaresInt_eq_zero_iff :
    ∀ xs : List Int, sumSquaresInt xs = 0 ↔ ∀ x ∈ xs, x = 0
  | [] => by simp [sumSquaresInt]
  | x :: xs => by
    simp only [sumSquaresInt, List.mem_cons, forall_eq_or_imp]
    have hx := sq_nonneg_int x
    have hxs := sumSquaresInt_nonneg xs
    constructor
    · intro h
      exact ⟨(sq_eq_zero_iff_int x).mp (by omega),
             (sumSquaresInt_eq_zero_iff xs).mp (by omega)⟩
    · rintro ⟨rfl, hrest⟩
      have hxs0 := (sumSquaresInt_eq_zero_iff xs).mpr hrest
      omega

/-! ## 3. Inequality Guards and Integer vs. Rational Witness Separation -/

def natLtWitness (a b : Nat) : Prop :=
  ∃ d : Nat, b = a + 1 + d

theorem natLtWitness_iff_lt (a b : Nat) :
    natLtWitness a b ↔ a < b :=
  ⟨by rintro ⟨d, hd⟩; omega, fun h => ⟨b - (a + 1), by omega⟩⟩

def natLeWitness (a b : Nat) : Prop :=
  ∃ d : Nat, b = a + d

theorem natLeWitness_iff_le (a b : Nat) :
    natLeWitness a b ↔ a ≤ b :=
  ⟨by rintro ⟨d, hd⟩; omega, fun h => ⟨b - a, by omega⟩⟩

def isFourSquaresInt (x : Int) : Prop :=
  ∃ a b c d : Int, x = a * a + b * b + c * c + d * d

theorem isFourSquaresInt_nonneg (x : Int) (h : isFourSquaresInt x) : 0 ≤ x := by
  rcases h with ⟨a, b, c, d, rfl⟩
  have := sq_nonneg_int a
  have := sq_nonneg_int b
  have := sq_nonneg_int c
  have := sq_nonneg_int d
  omega

/-- Over `ℤ`, `2 * w - 1 = 0` has no solution, whereas over `ℚ` the witness `(1, 2)`
    satisfies `2 * q.num - q.den = 0`. -/
theorem int_vs_rat_witness_separation :
    (¬ ∃ w : Int, 2 * w - 1 = 0) ∧
    (∃ q : QVal, 2 * q.num - (q.den : Int) = 0) :=
  ⟨by rintro ⟨w, hw⟩; omega, ⟨⟨1, 2, by decide⟩, rfl⟩⟩

/-! ## 4. Unreferenced Ambient Variables vs. Functional Witness Elimination -/

/-- A polynomial `P` has an unreferenced tail of `k` variables if its value depends
    only on the first `m` variables. -/
def IsUnreferencedTail {α β : Type} {m k : Nat}
    (P : α → (Fin (m + k) → β) → Int) : Prop :=
  ∀ (a : α) (w₁ w₂ : Fin (m + k) → β),
    (∀ i : Fin m, w₁ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩ =
                  w₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩) →
    P a w₁ = P a w₂

/-- Genuine functional witness elimination over `ℤ` (`y = f a x`). -/
theorem functional_witness_elimination_int {α : Type}
    (R : α → Int → Int → Prop) (f : α → Int → Int) :
    (∀ a : α, (∃ x y : Int, y = f a x ∧ R a x y) ↔ (∃ x : Int, R a x (f a x))) := by
  intro a
  exact ⟨by rintro ⟨x, _, rfl, hR⟩; exact ⟨x, hR⟩,
         by rintro ⟨x, hR⟩; exact ⟨x, f a x, rfl, hR⟩⟩

/-- Genuine functional subtraction elimination over `ℕ` (`w = s - v`) when `P` forces `v ≤ s`. -/
theorem functional_sub_elimination_nat
    (P : Nat → Nat → Nat → Prop)
    (h_le : ∀ s v : Nat, P s v (s - v) → v ≤ s) :
    ∀ s : Nat, (∃ v w : Nat, s = v + w ∧ P s v w) ↔ (∃ v : Nat, P s v (s - v)) := by
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
