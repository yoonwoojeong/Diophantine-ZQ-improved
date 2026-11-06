/-
  DiophantineZQ.lean
  ==================
  Machine-checked lemmas toward reducing the number of witnesses in Elliot Glazer's
  explicit Diophantine definition of ℤ in ℚ (`elliotglazer/diophantine-z-q`).

  Scope (see README): Sections 1-3 are component lemmas. Section 5 proves the
  total rational (ℚ) witness count of the Stage 1 circuit and its strict decrease,
  under Glazer's translator accounting. The semantic correctness of the Stage 1
  circuit (multi-slot packed equivalence) is not proved here.
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

/-! ## 5. Total ℚ-witness count before and after Stage 1

  Glazer's `rational-circuit-translator.js` (`Translator.translate`) turns the natural
  circuit `precision-natural-polynomial.json` into the `precision` recipe of
  `ordinary-integer-definition.json`. It allocates rational witnesses as follows:
  3 generator coordinates; for each explicit natural variable, 5 point coordinates
  (non-inputs only) and one `natural` guard block; for each distinct nontrivial
  constant, 5 + 1; for each `add` node, 5 + `raw_add`; for each `mul` node,
  5 + `multiply`; for each `power` call, 5 + `power_value`. All other recipes
  (`close`, `main`, `value_union`, `value`, `integers`) add a fixed 739,068 witnesses
  that do not depend on the natural circuit.

  The template sizes below are read from the pinned `ordinary-integer-definition.json`.
  The node counts of the baseline and Stage 1 circuits come from
  `scripts/stage1_circuit.js` (see README). -/

/-- Witnesses of the `natural` (four-square point-code) guard template. -/
def naturalGuardQ : ℕ := 140604
/-- Witnesses of the `raw_add` template. -/
def rawAddQ : ℕ := 6
/-- Witnesses of the `multiply` template. -/
def multiplyQ : ℕ := 35134
/-- Witnesses of the `power_value` recipe (one translated `power` template). -/
def powerValueQ : ℕ := 17786698
/-- Witnesses of each scalar-constant template. -/
def scalarConstantQ : ℕ := 1
/-- Distinct nontrivial constants in the precision circuit (unchanged by Stage 1). -/
def precisionConstants : ℕ := 4
/-- Witnesses outside the `precision` recipe. -/
def nonPrecisionQ : ℕ := 739068

/-- Size data of a five-input natural circuit, as counted by the translator. -/
structure NatCircuit where
  /-- explicit natural variables, including the 5 inputs -/
  vars : ℕ
  /-- `add` nodes -/
  adds : ℕ
  /-- `mul` nodes -/
  muls : ℕ
  /-- `power` template calls -/
  powers : ℕ
  deriving DecidableEq, Repr

/-- Rational witnesses of the `precision` recipe produced from circuit `c`. -/
def precisionQ (c : NatCircuit) : ℕ :=
  3 + 5 * (c.vars - 5) + c.vars * naturalGuardQ
    + precisionConstants * (5 + scalarConstantQ)
    + c.adds * (5 + rawAddQ) + c.muls * (5 + multiplyQ) + c.powers * (5 + powerValueQ)

/-- Total rational witnesses of the ordinary-integer definition built from circuit `c`. -/
def totalQ (c : NatCircuit) : ℕ := nonPrecisionQ + precisionQ c

/-- Glazer's pinned `precision-natural-polynomial.json`. -/
def glazerCircuit : NatCircuit := ⟨54056, 125327, 98382, 15845⟩

/-- The accounting reproduces Glazer's published witness count exactly. -/
theorem glazer_totalQ : totalQ glazerCircuit = 292890231904 := by decide

/-- Per-gadget sizes (variables, `add`, `mul`, `power`) removed and added by Stage 1.
    Removed per sub state: one `bitAnd(V_i, S_i, N_j)` (29, 66, 52, 9) and its
    top-level slot (+1 `add`, +1 `mul`). Removed per register: one
    `bitAnd(K N_j, R_j + D, K F)` with its arguments and slot, plus `N_j`
    (30, 68, 54, 9); `K F` is shared with `D + F = K F` and stays.
    Added per sub state: `mask(V_i, S_i)` and its slot (9, 20, 16, 3).
    Added per register tested by `n_j` sub states: fresh `M_j`, the equation
    `M_j + K Z_j = D + Z_j` with `Z_j = Σ W_i`, `mask(R_j, M_j)`, and their slots
    (10, 23 + n_j, 19, 3). -/
structure GadgetDelta where
  vars : ℕ
  adds : ℕ
  muls : ℕ
  powers : ℕ

def removedPerSub : GadgetDelta := ⟨29, 67, 53, 9⟩
def removedPerRegister : GadgetDelta := ⟨30, 68, 54, 9⟩
def addedPerSub : GadgetDelta := ⟨9, 20, 16, 3⟩
/-- Added for a register tested by `n` sub states. -/
def addedPerRegister (n : ℕ) : GadgetDelta := ⟨10, 23 + n, 19, 3⟩

/-- Stage 1 applied to a circuit whose `R` registers are each zero-tested by at least
    one of its `S` sub states. -/
def stage1Circuit (c : NatCircuit) (R S : ℕ) : NatCircuit :=
  ⟨c.vars - 20 * (R + S), c.adds - (45 * R + 46 * S),
   c.muls - (35 * R + 37 * S), c.powers - 6 * (R + S)⟩

/-- The deltas in `stage1Circuit` are the sums of the per-gadget sizes, where
    `Σ_j n_j = S` because every sub state tests exactly one register. -/
theorem stage1_delta_from_gadgets (R S : ℕ) :
    S * removedPerSub.vars + R * removedPerRegister.vars
        = (S * addedPerSub.vars + R * (addedPerRegister 0).vars) + 20 * (R + S) ∧
    S * removedPerSub.adds + R * removedPerRegister.adds
        = (S * addedPerSub.adds + (R * (addedPerRegister 0).adds + S)) + (45 * R + 46 * S) ∧
    S * removedPerSub.muls + R * removedPerRegister.muls
        = (S * addedPerSub.muls + R * (addedPerRegister 0).muls) + (35 * R + 37 * S) ∧
    S * removedPerSub.powers + R * removedPerRegister.powers
        = (S * addedPerSub.powers + R * (addedPerRegister 0).powers) + 6 * (R + S) := by
  simp only [removedPerSub, removedPerRegister, addedPerSub, addedPerRegister]
  omega

/-- Stage 1 removes `6(R + S)` power calls, matching `stage1_power_savings`. -/
theorem stage1Circuit_powers (states R S : ℕ) :
    (stage1Circuit ⟨0, 0, 0, baselinePowerCalls states R S⟩ R S).powers
      = stage1PowerCalls states R S := by
  simp only [stage1Circuit, baselinePowerCalls, stage1PowerCalls]
  omega

/-- ℚ witnesses saved by Stage 1 on a machine with `R` tested registers and `S` sub states. -/
def stage1QSavings (R S : ℕ) : ℕ :=
  20 * (R + S) * (5 + naturalGuardQ) + (45 * R + 46 * S) * (5 + rawAddQ)
    + (35 * R + 37 * S) * (5 + multiplyQ) + 6 * (R + S) * (5 + powerValueQ)

/-- Exact symbolic saving: for every circuit large enough to contain the removed
    gadgets, Stage 1 lowers the total ℚ-witness count by exactly `stage1QSavings R S`. -/
theorem stage1_totalQ_add_savings (c : NatCircuit) (R S : ℕ)
    (hv : 5 + 20 * (R + S) ≤ c.vars) (ha : 45 * R + 46 * S ≤ c.adds)
    (hm : 35 * R + 37 * S ≤ c.muls) (hp : 6 * (R + S) ≤ c.powers) :
    totalQ (stage1Circuit c R S) + stage1QSavings R S = totalQ c := by
  obtain ⟨v, a, m, p⟩ := c
  simp only at hv ha hm hp
  simp only [totalQ, precisionQ, stage1Circuit, stage1QSavings, naturalGuardQ, rawAddQ,
    multiplyQ, powerValueQ, scalarConstantQ, precisionConstants, nonPrecisionQ]
  omega

/-- Stage 1 strictly decreases the total ℚ-witness count whenever it removes at least
    one gadget. -/
theorem stage1_totalQ_lt (c : NatCircuit) (R S : ℕ) (hRS : 0 < R + S)
    (hv : 5 + 20 * (R + S) ≤ c.vars) (ha : 45 * R + 46 * S ≤ c.adds)
    (hm : 35 * R + 37 * S ≤ c.muls) (hp : 6 * (R + S) ≤ c.powers) :
    totalQ (stage1Circuit c R S) < totalQ c := by
  have h := stage1_totalQ_add_savings c R S hv ha hm hp
  have hpos : 0 < stage1QSavings R S := by
    simp only [stage1QSavings, naturalGuardQ, rawAddQ, multiplyQ, powerValueQ]
    omega
  omega

/-- The Stage 1 circuit for Glazer's machine (204 registers, all zero-tested;
    1,022 sub states). These are the counts produced by `scripts/stage1_circuit.js`. -/
theorem glazer_stage1_circuit :
    stage1Circuit glazerCircuit 204 1022 = ⟨29536, 69135, 53428, 8489⟩ := by decide

theorem glazer_stage1_totalQ :
    totalQ (stage1Circuit glazerCircuit 204 1022) = 157023255238 := by decide

/-- Total ℚ witnesses drop from 292,890,231,904 to 157,023,255,238. -/
theorem glazer_stage1_totalQ_lt :
    totalQ (stage1Circuit glazerCircuit 204 1022) < totalQ glazerCircuit := by decide

theorem glazer_stage1_Q_savings :
    totalQ glazerCircuit - totalQ (stage1Circuit glazerCircuit 204 1022) = 135866976666 ∧
    stage1QSavings 204 1022 = 135866976666 := by decide

end DiophantineZQ
