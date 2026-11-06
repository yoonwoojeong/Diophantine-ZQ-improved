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
theorem glazer_totalQ : totalQ glazerCircuit = 292890231904 := by sorry

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
        = (S * addedPerSub.powers + R * (addedPerRegister 0).powers) + 6 * (R + S) := by sorry

/-- Stage 1 removes `6(R + S)` power calls, matching `stage1_power_savings`. -/
theorem stage1Circuit_powers (states R S : ℕ) :
    (stage1Circuit ⟨0, 0, 0, baselinePowerCalls states R S⟩ R S).powers
      = stage1PowerCalls states R S := by sorry

/-- ℚ witnesses saved by Stage 1 on a machine with `R` tested registers and `S` sub states. -/
def stage1QSavings (R S : ℕ) : ℕ :=
  20 * (R + S) * (5 + naturalGuardQ) + (45 * R + 46 * S) * (5 + rawAddQ)
    + (35 * R + 37 * S) * (5 + multiplyQ) + 6 * (R + S) * (5 + powerValueQ)

/-- Exact symbolic saving: for every circuit large enough to contain the removed
    gadgets, Stage 1 lowers the total ℚ-witness count by exactly `stage1QSavings R S`. -/
theorem stage1_totalQ_add_savings (c : NatCircuit) (R S : ℕ)
    (hv : 5 + 20 * (R + S) ≤ c.vars) (ha : 45 * R + 46 * S ≤ c.adds)
    (hm : 35 * R + 37 * S ≤ c.muls) (hp : 6 * (R + S) ≤ c.powers) :
    totalQ (stage1Circuit c R S) + stage1QSavings R S = totalQ c := by sorry

/-- Stage 1 strictly decreases the total ℚ-witness count whenever it removes at least
    one gadget. -/
theorem stage1_totalQ_lt (c : NatCircuit) (R S : ℕ) (hRS : 0 < R + S)
    (hv : 5 + 20 * (R + S) ≤ c.vars) (ha : 45 * R + 46 * S ≤ c.adds)
    (hm : 35 * R + 37 * S ≤ c.muls) (hp : 6 * (R + S) ≤ c.powers) :
    totalQ (stage1Circuit c R S) < totalQ c := by sorry

/-- The Stage 1 circuit for Glazer's machine (204 registers, all zero-tested;
    1,022 sub states). These are the counts produced by `scripts/stage1_circuit.js`. -/
theorem glazer_stage1_circuit :
    stage1Circuit glazerCircuit 204 1022 = ⟨29536, 69135, 53428, 8489⟩ := by sorry

theorem glazer_stage1_totalQ :
    totalQ (stage1Circuit glazerCircuit 204 1022) = 157023255238 := by sorry

/-- Total ℚ witnesses drop from 292,890,231,904 to 157,023,255,238. -/
theorem glazer_stage1_totalQ_lt :
    totalQ (stage1Circuit glazerCircuit 204 1022) < totalQ glazerCircuit := by sorry

theorem glazer_stage1_Q_savings :
    totalQ glazerCircuit - totalQ (stage1Circuit glazerCircuit 204 1022) = 135866976666 ∧
    stage1QSavings 204 1022 = 135866976666 := by sorry

end DiophantineZQ
