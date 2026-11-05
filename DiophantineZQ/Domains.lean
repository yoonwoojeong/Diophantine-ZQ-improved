/-
  DiophantineZQ.Domains
  =====================
  Explicit domain preservation and Diophantine representation equivalences across
  ℕ (natural numbers), ℤ (integers), and ℚ (rationals), together with equation
  compression (sum-of-squares for conjunction over ℕ, ℤ, ℚ; product for disjunction)
  and strict preservation of integer vs. rational witness distinctions.
-/

namespace DiophantineZQ

/-! ## 1. Explicit Domain-Typed Diophantine Predicates -/

/-- A subset `S ⊆ ℕ^k` (represented as `α → Prop`) is Diophantine over `ℕ` with `m`
    natural witnesses if it is cut out by an existential quantifier over `Fin m → ℕ`
    of a polynomial equation `P(a, w) = Q(a, w)` (or equivalently an integer polynomial
    `R(a, w) = 0` evaluated at natural arguments). -/
def IsNatDiophantine {α : Type} (S : α → Prop) (m : Nat)
    (P : α → (Fin m → Nat) → Int) : Prop :=
  ∀ a : α, S a ↔ ∃ w : Fin m → Nat, P a w = 0

/-- A subset `S ⊆ α` is Diophantine over `ℤ` with `m` integer witnesses if it is cut out
    by an existential quantifier over `Fin m → Int` of an integer equation `P(a, z) = 0`. -/
def IsIntDiophantine {α : Type} (S : α → Prop) (m : Nat)
    (P : α → (Fin m → Int) → Int) : Prop :=
  ∀ a : α, S a ↔ ∃ z : Fin m → Int, P a z = 0

/-- A rational number `q` is represented here by an explicit numerator/denominator pair
    `(num, den)` with `den > 0` in lowest terms (or general formal rationals), or via
    integer homogeneous equations after denominator clearing. To avoid external package
    dependencies while remaining 100% kernel-checked in core Lean 4, we also define a
    lightweight `QVal` structure with exact field equality. -/
structure QVal where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

namespace QVal

/-- Equality of rational values `a.num / a.den = b.num / b.den`. -/
def EqRat (a b : QVal) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

/-- Embed an integer `z : Int` as a rational `z / 1`. -/
def ofInt (z : Int) : QVal :=
  ⟨z, 1, Nat.one_pos⟩

/-- A rational `q : QVal` represents an ordinary integer (`q ∈ ℤ ⊆ ℚ`) iff
    there exists `z : Int` such that `q.num = z * q.den`. -/
def IsInteger (q : QVal) : Prop :=
  ∃ z : Int, q.num = z * (q.den : Int)

theorem ofInt_isInteger (z : Int) : IsInteger (ofInt z) := by
  refine ⟨z, ?_⟩
  simp [ofInt]

theorem isInteger_iff_eqRat_ofInt (q : QVal) :
    IsInteger q ↔ ∃ z : Int, EqRat q (ofInt z) := by
  unfold IsInteger EqRat ofInt
  simp

end QVal

/-! ## 2. Sum-of-Squares Conjunction & Product Disjunction over ℤ -/

theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : x ≤ 0 := by omega
    have h'' : 0 ≤ -x := by omega
    have heq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul_neg]
    rw [← heq]
    exact Int.mul_nonneg h'' h''

theorem sq_eq_zero_iff_int (x : Int) : x * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases Int.mul_eq_zero.mp h with hx | hx <;> exact hx
  · intro h
    subst h
    rfl

/-- Conjoining two integer equations `A = 0 ∧ B = 0` into a single equation
    `A^2 + B^2 = 0` requires ZERO additional existential witnesses and multiplies
    total degree by 2. -/
theorem sq_add_sq_eq_zero_iff_int (a b : Int) :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  have ha : 0 ≤ a * a := sq_nonneg_int a
  have hb : 0 ≤ b * b := sq_nonneg_int b
  constructor
  · intro h
    have ha0 : a * a = 0 := by omega
    have hb0 : b * b = 0 := by omega
    exact ⟨(sq_eq_zero_iff_int a).mp ha0, (sq_eq_zero_iff_int b).mp hb0⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Disjoining two integer equations `A = 0 ∨ B = 0` into a single equation
    `A * B = 0` requires ZERO additional existential witnesses (when witness blocks
    are already declared or shared) and sums the degrees of `A` and `B`. -/
theorem mul_eq_zero_iff_int (a b : Int) :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  Int.mul_eq_zero

/-- Recursive sum of squares of a list of integer residuals. -/
def sumSquaresInt : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSquaresInt xs

theorem sumSquaresInt_nonneg : ∀ xs : List Int, 0 ≤ sumSquaresInt xs
  | [] => Int.le_refl 0
  | x :: xs => Int.add_nonneg (sq_nonneg_int x) (sumSquaresInt_nonneg xs)

/-- An `n`-ary system of integer equations `xs = [e_1, ..., e_n]` vanishes simultaneously
    if and only if `sumSquaresInt xs = 0`. -/
theorem sumSquaresInt_eq_zero_iff :
    ∀ xs : List Int, sumSquaresInt xs = 0 ↔ ∀ x ∈ xs, x = 0
  | [] => by simp [sumSquaresInt]
  | x :: xs => by
    simp only [sumSquaresInt, List.mem_cons, forall_eq_or_imp]
    have hx := sq_nonneg_int x
    have hxs := sumSquaresInt_nonneg xs
    constructor
    · intro h
      have hx0 : x * x = 0 := by omega
      have hxs0 : sumSquaresInt xs = 0 := by omega
      exact ⟨(sq_eq_zero_iff_int x).mp hx0, (sumSquaresInt_eq_zero_iff xs).mp hxs0⟩
    · rintro ⟨rfl, hrest⟩
      have hxs0 : sumSquaresInt xs = 0 := (sumSquaresInt_eq_zero_iff xs).mpr hrest
      omega

/-! ## 3. Strict Inequality and Non-negativity Guards over ℕ vs ℤ vs ℚ -/

/-- Over `ℕ`, strict inequality `a < b` is represented by a single natural witness `d : ℕ`
    via `b = a + 1 + d` (the exact `Builder.lt` macro in `integer-diophantine-compiler.js`). -/
def natLtWitness (a b : Nat) : Prop :=
  ∃ d : Nat, b = a + 1 + d

theorem natLtWitness_iff_lt (a b : Nat) :
    natLtWitness a b ↔ a < b := by
  unfold natLtWitness
  constructor
  · rintro ⟨d, hd⟩
    omega
  · intro h
    refine ⟨b - (a + 1), ?_⟩
    omega

/-- Over `ℕ`, non-strict inequality `a ≤ b` is represented by a single natural witness `d : ℕ`
    via `b = a + d` (`Builder.le`). -/
def natLeWitness (a b : Nat) : Prop :=
  ∃ d : Nat, b = a + d

theorem natLeWitness_iff_le (a b : Nat) :
    natLeWitness a b ↔ a ≤ b := by
  unfold natLeWitness
  constructor
  · rintro ⟨d, hd⟩
    omega
  · intro h
    refine ⟨b - a, ?_⟩
    omega

/-- Over `ℤ`, a four-square representation `x = a^2 + b^2 + c^2 + d^2` always guarantees
    `0 ≤ x` (soundness of Lagrange's four-square guard). Note that over `ℚ`, a sum of four
    rational squares is also always non-negative, which is why `diophantine-z-q` CANNOT
    define `ℕ ⊆ ℚ` purely by four rational squares, and instead must apply four squares
    inside its discrete elliptic index model `D` (`natural` template = 4 `multiply` calls
    + 3 `raw_add` calls = 140,604 rational witnesses per natural variable!). -/
def isFourSquaresInt (x : Int) : Prop :=
  ∃ a b c d : Int, x = a * a + b * b + c * c + d * d

theorem isFourSquaresInt_nonneg (x : Int) (h : isFourSquaresInt x) : 0 ≤ x := by
  rcases h with ⟨a, b, c, d, rfl⟩
  have ha := sq_nonneg_int a
  have hb := sq_nonneg_int b
  have hc := sq_nonneg_int c
  have hd := sq_nonneg_int d
  omega

/-- Crucial distinction between integer witnesses and rational witnesses:
    The equation `2 * w = 1` has NO solution `w : Int`, whereas over `ℚ` the witness
    `q = (1, 2)` satisfies the cleared rational equation `2 * q.num = 1 * q.den`.
    This witnesses that replacing `∃ w ∈ ℤ` with `∃ w ∈ ℚ` in a polynomial equation
    strictly enlarges the projection unless guarded by an arithmetic model of `ℤ` in `ℚ`. -/
theorem int_vs_rat_witness_separation :
    (¬ ∃ w : Int, 2 * w - 1 = 0) ∧
    (∃ q : QVal, 2 * q.num - (q.den : Int) = 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    omega
  · refine ⟨⟨1, 2, by decide⟩, ?_⟩
    rfl

/-! ## 4. Unused (Ambient) vs. Genuine Variable Elimination -/

/-- Suppose `P : α → (Fin (m + k) → β) → Int` does not depend on the last `k` witness
    coordinates (they are unreferenced/ambient variables, such as the 14 unreferenced
    parameters of `multiply.guard` in `ordinary-integer-definition.json`).
    Projecting onto the `m` active witnesses preserves the defined relation identically,
    provided `β` is inhabited. However, per our audit policy, pruning unreferenced
    ambient variables is recorded as dead-variable cleanup rather than a genuine
    mathematical witness reduction. -/
def IsUnreferencedTail {α β : Type} {m k : Nat}
    (P : α → (Fin (m + k) → β) → Int) : Prop :=
  ∀ (a : α) (w₁ w₂ : Fin (m + k) → β),
    (∀ i : Fin m, w₁ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩ =
                  w₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m k)⟩) →
    P a w₁ = P a w₂

/-- Conversely, a **functional witness substitution** (such as eliminating `W_i` via
    `S_i = V_i + W_i` over `ℤ` or eliminating `D` via `D = (K - 1) * F_q`) genuinely
    eliminates an active variable that appears nontrivially in the polynomial system. -/
theorem functional_witness_elimination_int {α : Type}
    (R : α → Int → Int → Prop) (f : α → Int → Int) :
    (∀ a : α, (∃ x y : Int, y = f a x ∧ R a x y) ↔ (∃ x : Int, R a x (f a x))) := by
  intro a
  constructor
  · rintro ⟨x, y, rfl, hR⟩
    exact ⟨x, hR⟩
  · rintro ⟨x, hR⟩
    exact ⟨x, f a x, rfl, hR⟩

/-- Over `ℕ`, functional witness elimination `w = s - v` (such as `W_i = S_i - V_i` in
    `S_i = V_i + W_i`) eliminates the witness `w` without even needing an extra `v ≤ s`
    inequality witness whenever the remaining constraints `P s v` already force `v ≤ s`
    (for instance, when `V_i ≼ S_i` or `V_i = S_i &&& N_j`). -/
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
    refine ⟨v, s - v, by omega, hP⟩

end DiophantineZQ
