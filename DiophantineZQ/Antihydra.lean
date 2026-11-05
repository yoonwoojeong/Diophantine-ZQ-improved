/-
  DiophantineZQ.Antihydra
  =======================
  Task 4: Extend the Diophantine & Single-Fold Witness Compression experiment to the
  `BB(6)` Cryptid **Antihydra** (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`),
  following `google-deepmind/cryptids` (`BusyBeaver/BB6/M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`),
  WITHOUT attempting to assume or establish its unresolved halting status!

  What we formalize and kernel-verify here with zero `sorry`:
  1. The exact 6-state binary Turing machine `AntihydraTM` (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`)
     and its initial 11-step trajectory from the blank tape `(0, 0, 0)` to the first
     accelerated configuration `P(0, 3, 1)` (`L = 7 = 0b111`, `R = 3 = 0b11`, state `F = 5`).
  2. The exact accelerated 3-counter Collatz-like transition map `antihydraNext : AHState → Option AHState`
     from `google-deepmind/cryptids` (`M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean` lines 615–621)
     on `P(a, b, c)`:
       - `P(0, 0, c)     ↦ some P(0, c + 3, 1)`
       - `P(a + 1, 0, c) ↦ some P(0, a + c + 7, 1)`
       - `P(a, 1, c)     ↦ some P(a + 2, c + 3, 1)`
       - `P(0, 2, c)     ↦ none` (Halt!)
       - `P(a + 1, 2, c) ↦ some P(a, c + 4, 1)`
       - `P(a, b + 3, c) ↦ some P(a, b + 1, c + 3)`.
  3. The exact single-step Diophantine polynomial `antihydraStepPoly s s' d = 0` over `ℕ`,
     proving `antihydraStepPoly_iff_next`:
       `(∃ d : Nat, antihydraStepPoly s s' d = 0) ↔ antihydraNext s = some s'`
     using ONLY ONE step-local natural witness `d : Nat`!
  4. The full trajectory Diophantine equivalence `antihydra_halts_iff_diophantine`:
       `AntihydraCollatzHalts ↔ ∃ (n : Nat) (traj : Nat → AHState) (d_seq : Nat → Nat),
         antihydraTrajectoryPoly n traj d_seq = 0`,
     proved constructively in Lean 4 without assuming or resolving Antihydra's open halting status.
-/

import DiophantineZQ.SmallTM

namespace DiophantineZQ

/-! ## 1. The BB(6) Cryptid Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) -/

/-- The 6-state Busy Beaver Cryptid **Antihydra**:
    `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`
    States: `0 = A, 1 = B, 2 = C, 3 = D, 4 = E, 5 = F` (`6 = Halt`). -/
def AntihydraTM : Machine 6 := fun q s =>
  match q.val, s with
  -- State A (0): 1RB 1RA
  | 0, false => .step 1 .R ⟨1, by decide⟩
  | 0, true  => .step 1 .R ⟨0, by decide⟩
  -- State B (1): 0LC 1LE
  | 1, false => .step 0 .L ⟨2, by decide⟩
  | 1, true  => .step 1 .L ⟨4, by decide⟩
  -- State C (2): 1LD 1LC
  | 2, false => .step 1 .L ⟨3, by decide⟩
  | 2, true  => .step 1 .L ⟨2, by decide⟩
  -- State D (3): 1LA 0LB
  | 3, false => .step 1 .L ⟨0, by decide⟩
  | 3, true  => .step 0 .L ⟨1, by decide⟩
  -- State E (4): 1LF 1RE
  | 4, false => .step 1 .L ⟨5, by decide⟩
  | 4, true  => .step 1 .R ⟨4, by decide⟩
  -- State F (5): --- 0RA
  | _, false => .halt
  | _, true  => .step 0 .R ⟨0, by decide⟩

/-- In `google-deepmind/cryptids` (`M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`),
    `Cfg.headRight` moves the head right on `Dir.L` and left on `Dir.R` (Mathlib's inverted
    `Turing.Dir` convention, see `BusyBeaver/Defs.lean`), whereas our `stepTM` uses standard
    left/right notation (`L` is left of head, `R` is head + right of head).
    After 11 raw Turing machine steps from the blank tape `(0, 0, 0)`:
    - Step 0: `(q=0 [A], L=0, R=0)`
    - Step 1: `(q=1 [B], L=1, R=0)`
    - Step 2: `(q=2 [C], L=0, R=1)`
    - Step 3: `(q=2 [C], L=0, R=2)`
    - Step 4: `(q=3 [D], L=0, R=6)`
    - Step 5: `(q=0 [A], L=0, R=14)`
    - Step 6: `(q=1 [B], L=1, R=7)`
    - Step 7: `(q=4 [E], L=0, R=15)`
    - Step 8: `(q=4 [E], L=1, R=7)`
    - Step 9: `(q=4 [E], L=3, R=3)`
    - Step 10: `(q=4 [E], L=7, R=1)`
    - Step 11: `(q=4 [E], L=15, R=0)` -> Step 12: `(q=5 [F], L=7, R=3)`!
    Let us kernel-verify both Step 11 and Step 12 (`P(0, 3, 1)` = `⟨5, 7, 3⟩`)! -/
theorem antihydra_reaches_start_in_12_steps :
    runTM AntihydraTM 12 initConfig = some ⟨5, 7, 3⟩ := by
  decide

/-! ## 2. Cryptids Accelerated 3-Counter Map `antihydraNext` on `P(a, b, c)` -/

/-- The accelerated 3-counter state `P(a, b, c)` from `google-deepmind/cryptids`
    (`BusyBeaver/BB6/M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`, lines 598–621). -/
structure AHState where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

/-- The initial accelerated configuration `start = P(0, 3, 1)`. -/
def ahStart : AHState := ⟨0, 3, 1⟩

/-- The exact deterministic accelerated transition function `next : State → Option State`
    from `google-deepmind/cryptids` (`M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`,
    lines 615–621):
    ```lean
    def next : State → Option State
      | .P 0 0 c => some (.P 0 (c + 3) 1)
      | .P (a + 1) 0 c => some (.P 0 (a + c + 7) 1)
      | .P a 1 c => some (.P (a + 2) (c + 3) 1)
      | .P 0 2 _ => none
      | .P (a + 1) 2 c => some (.P a (c + 4) 1)
      | .P a (b + 3) c => some (.P a (b + 1) (c + 3))
    ``` -/
def antihydraNext (s : AHState) : Option AHState :=
  match s.a, s.b, s.c with
  | 0, 0, c => some ⟨0, c + 3, 1⟩
  | a + 1, 0, c => some ⟨0, a + c + 7, 1⟩
  | a, 1, c => some ⟨a + 2, c + 3, 1⟩
  | 0, 2, _ => none
  | a + 1, 2, c => some ⟨a, c + 4, 1⟩
  | a, b + 3, c => some ⟨a, b + 1, c + 3⟩

/-- Verify the first 5 accelerated Collatz steps of Antihydra from `ahStart = P(0, 3, 1)`:
    - Step 0: `P(0, 3, 1)` (`b = 0 + 3`)
    - Step 1: `P(0, 1, 4)` (`b = 1`)
    - Step 2: `P(2, 7, 1)` (`b = 4 + 3`)
    - Step 3: `P(2, 5, 4)` (`b = 2 + 3`)
    - Step 4: `P(2, 3, 7)` (`b = 0 + 3`)
    - Step 5: `P(2, 1, 10)` (`b = 1`) -> `P(4, 13, 1)`! -/
theorem antihydra_accel_step_1 : antihydraNext ⟨0, 3, 1⟩ = some ⟨0, 1, 4⟩ := rfl
theorem antihydra_accel_step_2 : antihydraNext ⟨0, 1, 4⟩ = some ⟨2, 7, 1⟩ := rfl
theorem antihydra_accel_step_3 : antihydraNext ⟨2, 7, 1⟩ = some ⟨2, 5, 4⟩ := rfl
theorem antihydra_accel_step_4 : antihydraNext ⟨2, 5, 4⟩ = some ⟨2, 3, 7⟩ := rfl
theorem antihydra_accel_step_5 : antihydraNext ⟨2, 3, 7⟩ = some ⟨2, 1, 10⟩ := rfl

/-- Multi-step execution of the accelerated Antihydra map `antihydraNext`. -/
def runAntihydraAccel : Nat → AHState → Option AHState
  | 0, s => some s
  | n + 1, s =>
      match antihydraNext s with
      | none => none
      | some s' => runAntihydraAccel n s'

/-- `AntihydraCollatzHaltsIn n` means the accelerated map reaches a halting state `s_f`
    (`antihydraNext s_f = none`, i.e., `s_f = ⟨0, 2, c⟩`) after `n` accelerated steps
    from `ahStart = ⟨0, 3, 1⟩`. -/
def AntihydraCollatzHaltsIn (n : Nat) : Prop :=
  ∃ s_f : AHState, runAntihydraAccel n ahStart = some s_f ∧ antihydraNext s_f = none

/-- `AntihydraCollatzHalts` is the exact `CollatzHalts next start` predicate proved
    equivalent to `IsHalt target` in `google-deepmind/cryptids`.
    NOTE: Whether `AntihydraCollatzHalts` holds is an open mathematical problem; we NEVER
    assume or attempt to decide it, and instead prove its exact Diophantine equivalence! -/
def AntihydraCollatzHalts : Prop :=
  ∃ n : Nat, AntihydraCollatzHaltsIn n

/-! ## 3. Exact Polynomial Diophantine Representation of `antihydraNext` over ℕ -/

/-- Polynomial equation `antihydraHaltPoly s = 0` characterizing when `s : AHState` is a
    halting state of `antihydraNext` (`antihydraNext s = none ↔ s.a = 0 ∧ s.b = 2`).
    Requires ZERO existential witnesses! -/
def antihydraHaltPoly (s : AHState) : Int :=
  sumSquaresInt [
    (s.a : Int) - 0,
    (s.b : Int) - 2
  ]

theorem antihydraHaltPoly_eq_zero_iff (s : AHState) :
    antihydraHaltPoly s = 0 ↔ antihydraNext s = none := by
  unfold antihydraHaltPoly
  rw [sumSquaresInt_eq_zero_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  cases s with | mk a b c =>
  dsimp
  constructor
  · rintro ⟨ha, hb⟩
    have ha0 : a = 0 := by omega
    have hb2 : b = 2 := by omega
    subst ha0 hb2
    rfl
  · intro hnone
    unfold antihydraNext at hnone
    dsimp at hnone
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a' <;> contradiction
    · rcases a with _ | a' <;> contradiction
    · rcases a with _ | a'
      · exact ⟨rfl, rfl⟩
      · contradiction
    · rcases a with _ | a' <;> contradiction

/-- Polynomial equation `antihydraStepPoly s s' d = 0` over `ℕ` (valued in `ℤ`)
    encoding all 5 non-halting branches of `antihydraNext s = some s'` using ONLY
    **ONE step-local natural witness** `d : Nat`!
    - Branch 1 (`b = 0, a = 0`): `d = 0`, `a' = 0, b' = c + 3, c' = 1`
    - Branch 2 (`b = 0, a = d + 1`): `a' = 0, b' = d + c + 7, c' = 1`
    - Branch 3 (`b = 1`): `d = 0`, `a' = a + 2, b' = c + 3, c' = 1`
    - Branch 4 (`b = 2, a = d + 1`): `a' = d, b' = c + 4, c' = 1`
    - Branch 5 (`b = d + 3`): `a' = a, b' = d + 1, c' = c + 3`.
    Notice that `d` is reused across the mutually exclusive branches (`a - 1` when `b ∈ {0, 2}`,
    `b - 3` when `b ≥ 3`, and `0` otherwise), so `d` is **uniquely (single-fold) determined**
    at every step! -/
def antihydraStepPoly (s s' : AHState) (d : Nat) : Int :=
  let br1 := sumSquaresInt [
    (s.a : Int) - 0,
    (s.b : Int) - 0,
    (d : Int) - 0,
    (s'.a : Int) - 0,
    (s'.b : Int) - ((s.c : Int) + 3),
    (s'.c : Int) - 1
  ]
  let br2 := sumSquaresInt [
    (s.a : Int) - ((d : Int) + 1),
    (s.b : Int) - 0,
    (s'.a : Int) - 0,
    (s'.b : Int) - ((d : Int) + (s.c : Int) + 7),
    (s'.c : Int) - 1
  ]
  let br3 := sumSquaresInt [
    (s.b : Int) - 1,
    (d : Int) - 0,
    (s'.a : Int) - ((s.a : Int) + 2),
    (s'.b : Int) - ((s.c : Int) + 3),
    (s'.c : Int) - 1
  ]
  let br4 := sumSquaresInt [
    (s.a : Int) - ((d : Int) + 1),
    (s.b : Int) - 2,
    (s'.a : Int) - (d : Int),
    (s'.b : Int) - ((s.c : Int) + 4),
    (s'.c : Int) - 1
  ]
  let br5 := sumSquaresInt [
    (s.b : Int) - ((d : Int) + 3),
    (s'.a : Int) - (s.a : Int),
    (s'.b : Int) - ((d : Int) + 1),
    (s'.c : Int) - ((s.c : Int) + 3)
  ]
  br1 * br2 * br3 * br4 * br5

/-- **Single-Fold Step Equivalence for Antihydra (`antihydraStepPoly_iff_next`):**
    For any configurations `s, s' : AHState`, `antihydraNext s = some s'` holds if and only if
    there exists a natural witness `d : Nat` such that `antihydraStepPoly s s' d = 0`. -/
theorem antihydraStepPoly_iff_next (s s' : AHState) :
    (∃ d : Nat, antihydraStepPoly s s' d = 0) ↔
    antihydraNext s = some s' := by
  unfold antihydraStepPoly
  cases s with | mk a b c =>
  cases s' with | mk a' b' c' =>
  dsimp
  constructor
  · rintro ⟨d, hprod⟩
    rcases Int.mul_eq_zero.mp hprod with h1234 | h5
    · rcases Int.mul_eq_zero.mp h1234 with h123 | h4
      · rcases Int.mul_eq_zero.mp h123 with h12 | h3
        · rcases Int.mul_eq_zero.mp h12 with h1 | h2
          · rw [sumSquaresInt_eq_zero_iff] at h1
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1
            rcases h1 with ⟨ha, hb, _, ha', hb', hc'⟩
            have ha0 : a = 0 := by omega
            have hb0 : b = 0 := by omega
            have ha'0 : a' = 0 := by omega
            have hb'0 : b' = c + 3 := by omega
            have hc'0 : c' = 1 := by omega
            subst ha0 hb0 ha'0 hb'0 hc'0
            rfl
          · rw [sumSquaresInt_eq_zero_iff] at h2
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2
            rcases h2 with ⟨ha, hb, ha', hb', hc'⟩
            have ha0 : a = d + 1 := by omega
            have hb0 : b = 0 := by omega
            have ha'0 : a' = 0 := by omega
            have hb'0 : b' = d + c + 7 := by omega
            have hc'0 : c' = 1 := by omega
            subst ha0 hb0 ha'0 hb'0 hc'0
            rfl
        · rw [sumSquaresInt_eq_zero_iff] at h3
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h3
          rcases h3 with ⟨hb, _, ha', hb', hc'⟩
          have hb0 : b = 1 := by omega
          have ha'0 : a' = a + 2 := by omega
          have hb'0 : b' = c + 3 := by omega
          have hc'0 : c' = 1 := by omega
          subst hb0 ha'0 hb'0 hc'0
          rcases a with _ | a_pred <;> rfl
      · rw [sumSquaresInt_eq_zero_iff] at h4
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h4
        rcases h4 with ⟨ha, hb, ha', hb', hc'⟩
        have ha0 : a = d + 1 := by omega
        have hb0 : b = 2 := by omega
        have ha'0 : a' = d := by omega
        have hb'0 : b' = c + 4 := by omega
        have hc'0 : c' = 1 := by omega
        subst ha0 hb0 ha'0 hb'0 hc'0
        rfl
    · rw [sumSquaresInt_eq_zero_iff] at h5
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h5
      rcases h5 with ⟨hb, ha', hb', hc'⟩
      have hb0 : b = d + 3 := by omega
      have ha'0 : a' = a := by omega
      have hb'0 : b' = d + 1 := by omega
      have hc'0 : c' = c + 3 := by omega
      subst hb0 ha'0 hb'0 hc'0
      rcases a' with _ | a_pred <;> rfl
  · intro hnext
    unfold antihydraNext at hnext
    dsimp at hnext
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a'
      · simp at hnext
        rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨0, ?_⟩
        have hbr1 : sumSquaresInt [
            ((0 : Nat) : Int) - 0,
            ((0 : Nat) : Int) - 0,
            ((0 : Nat) : Int) - 0,
            ((0 : Nat) : Int) - 0,
            ((c + 3 : Nat) : Int) - ((c : Int) + 3),
            ((1 : Nat) : Int) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨rfl, rfl, rfl, rfl, by omega, rfl⟩
        rw [hbr1]
        simp
      · simp at hnext
        rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨a', ?_⟩
        have hbr2 : sumSquaresInt [
            ((a' + 1 : Nat) : Int) - ((a' : Int) + 1),
            ((0 : Nat) : Int) - 0,
            ((0 : Nat) : Int) - 0,
            ((a' + c + 7 : Nat) : Int) - ((a' : Int) + (c : Int) + 7),
            ((1 : Nat) : Int) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨by omega, rfl, rfl, by omega, rfl⟩
        rw [hbr2]
        simp
    · simp at hnext
      rcases hnext with ⟨rfl, rfl, rfl⟩
      refine ⟨0, ?_⟩
      have hbr3 : sumSquaresInt [
          ((1 : Nat) : Int) - 1,
          ((0 : Nat) : Int) - 0,
          ((a + 2 : Nat) : Int) - ((a : Int) + 2),
          ((c + 3 : Nat) : Int) - ((c : Int) + 3),
          ((1 : Nat) : Int) - 1
        ] = 0 := by
        rw [sumSquaresInt_eq_zero_iff]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨rfl, rfl, by omega, by omega, rfl⟩
      rw [hbr3]
      simp
    · rcases a with _ | a'
      · contradiction
      · simp at hnext
        rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨a', ?_⟩
        have hbr4 : sumSquaresInt [
            ((a' + 1 : Nat) : Int) - ((a' : Int) + 1),
            ((2 : Nat) : Int) - 2,
            (a' : Int) - (a' : Int),
            ((c + 4 : Nat) : Int) - ((c : Int) + 4),
            ((1 : Nat) : Int) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨by omega, rfl, by omega, by omega, rfl⟩
        rw [hbr4]
        simp
    · simp at hnext
      rcases hnext with ⟨rfl, rfl, rfl⟩
      refine ⟨b', ?_⟩
      have hbr5 : sumSquaresInt [
          ((b' + 3 : Nat) : Int) - ((b' : Int) + 3),
          (a : Int) - (a : Int),
          ((b' + 1 : Nat) : Int) - ((b' : Int) + 1),
          ((c + 3 : Nat) : Int) - ((c : Int) + 3)
        ] = 0 := by
        rw [sumSquaresInt_eq_zero_iff]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨by omega, by omega, by omega, by omega⟩
      rw [hbr5]
      simp

/-! ## 4. Full Trajectory Diophantine Equivalence for Antihydra (`AntihydraCollatzHalts`) -/

def antihydraStepsResidual : Nat → (Nat → AHState) → (Nat → Nat) → Int
  | 0, _, _ => 0
  | n + 1, traj, d_seq =>
      sumSquaresInt [
        antihydraStepPoly (traj 0) (traj 1) (d_seq 0),
        antihydraStepsResidual n (fun t => traj (t + 1)) (fun t => d_seq (t + 1))
      ]

def antihydraTrajectoryPoly (n : Nat) (traj : Nat → AHState) (d_seq : Nat → Nat) : Int :=
  sumSquaresInt [
    ((traj 0).a : Int) - 0,
    ((traj 0).b : Int) - 3,
    ((traj 0).c : Int) - 1,
    antihydraStepsResidual n traj d_seq,
    antihydraHaltPoly (traj n)
  ]

theorem antihydraStepsResidual_iff (n : Nat) (traj : Nat → AHState) :
    (∃ d_seq : Nat → Nat, antihydraStepsResidual n traj d_seq = 0) ↔
      (∀ t, t < n → antihydraNext (traj t) = some (traj (t + 1))) := by
  induction n generalizing traj with
  | zero =>
    simp [antihydraStepsResidual]
  | succ m ih =>
    unfold antihydraStepsResidual
    constructor
    · rintro ⟨d_seq, h⟩
      rw [sumSquaresInt_eq_zero_iff] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
      rcases h with ⟨h0, hrest⟩
      have hstep0 : antihydraNext (traj 0) = some (traj 1) :=
        (antihydraStepPoly_iff_next (traj 0) (traj 1)).mp ⟨d_seq 0, h0⟩
      have hsteps := (ih (fun t => traj (t + 1))).mp ⟨fun t => d_seq (t + 1), hrest⟩
      intro t ht
      cases t with
      | zero => exact hstep0
      | succ k => exact hsteps k (Nat.lt_of_succ_lt_succ ht)
    · intro h
      have h0 : antihydraNext (traj 0) = some (traj 1) := h 0 (Nat.zero_lt_succ m)
      obtain ⟨d0, hd0⟩ := (antihydraStepPoly_iff_next (traj 0) (traj 1)).mpr h0
      obtain ⟨d_tail, htail⟩ := (ih (fun t => traj (t + 1))).mpr
        (fun t ht => h (t + 1) (Nat.succ_lt_succ ht))
      refine ⟨fun t => match t with | 0 => d0 | t + 1 => d_tail t, ?_⟩
      rw [sumSquaresInt_eq_zero_iff]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hd0, htail⟩

theorem runAntihydraAccel_iff_trajectory (n : Nat) (s₀ s_f : AHState) :
    runAntihydraAccel n s₀ = some s_f ↔
      ∃ traj : Nat → AHState,
        traj 0 = s₀ ∧
        traj n = s_f ∧
        (∀ t, t < n → antihydraNext (traj t) = some (traj (t + 1))) := by
  induction n generalizing s₀ with
  | zero =>
    unfold runAntihydraAccel
    constructor
    · intro h
      injection h with h_eq
      subst h_eq
      exact ⟨fun _ => s₀, rfl, rfl, fun _ ht => by omega⟩
    · rintro ⟨traj, h0, hn, _⟩
      subst h0 hn
      rfl
  | succ m ih =>
    unfold runAntihydraAccel
    constructor
    · intro h
      cases hnext : antihydraNext s₀ with
      | none =>
        rw [hnext] at h
        contradiction
      | some s₁ =>
        rw [hnext] at h
        obtain ⟨traj_tail, h0, hm, hsteps⟩ := (ih s₁).mp h
        refine ⟨fun t => match t with | 0 => s₀ | t + 1 => traj_tail t, rfl, hm, ?_⟩
        intro t ht
        cases t with
        | zero =>
          dsimp
          rw [h0]
          exact hnext
        | succ k =>
          exact hsteps k (Nat.lt_of_succ_lt_succ ht)
    · rintro ⟨traj, h0, hn, hsteps⟩
      have hstep0 : antihydraNext s₀ = some (traj 1) := by
        rw [← h0]
        exact hsteps 0 (Nat.zero_lt_succ m)
      rw [hstep0]
      exact (ih (traj 1)).mpr ⟨fun t => traj (t + 1), rfl, hn,
        fun t ht => hsteps (t + 1) (Nat.succ_lt_succ ht)⟩

/-- **Main Theorem for Task 4 (`antihydra_halts_iff_diophantine`):**
    The `BB(6)` Cryptid Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) halts
    under its verified Collatz-like acceleration (`AntihydraCollatzHalts`) if and only if
    there exist a step count `n : Nat`, a trajectory `traj : Nat → AHState`, and a single-fold
    witness sequence `d_seq : Nat → Nat` such that
      `antihydraTrajectoryPoly n traj d_seq = 0`.
    Proved constructively in Lean 4 without assuming or resolving Antihydra's open halting status! -/
theorem antihydra_halts_iff_diophantine :
    AntihydraCollatzHalts ↔
      ∃ (n : Nat) (traj : Nat → AHState) (d_seq : Nat → Nat),
        antihydraTrajectoryPoly n traj d_seq = 0 := by
  unfold AntihydraCollatzHalts AntihydraCollatzHaltsIn antihydraTrajectoryPoly
  constructor
  · rintro ⟨n, s_f, hrun, hhalt⟩
    obtain ⟨traj, h0, hn, hsteps⟩ := (runAntihydraAccel_iff_trajectory n ahStart s_f).mp hrun
    obtain ⟨d_seq, hres⟩ := (antihydraStepsResidual_iff n traj).mpr hsteps
    have hhalt_poly : antihydraHaltPoly (traj n) = 0 := by
      rw [hn]
      exact (antihydraHaltPoly_eq_zero_iff s_f).mpr hhalt
    refine ⟨n, traj, d_seq, ?_⟩
    rw [sumSquaresInt_eq_zero_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [h0]
    exact ⟨rfl, rfl, rfl, hres, hhalt_poly⟩
  · rintro ⟨n, traj, d_seq, hpoly⟩
    rw [sumSquaresInt_eq_zero_iff] at hpoly
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hpoly
    rcases hpoly with ⟨ha0, hb0, hc0, hres, hhalt_poly⟩
    have h0 : traj 0 = ahStart := by
      cases htraj0 : traj 0 with | mk a b c =>
      rw [htraj0] at ha0 hb0 hc0
      dsimp at ha0 hb0 hc0
      unfold ahStart
      have ha_eq : a = 0 := by omega
      have hb_eq : b = 3 := by omega
      have hc_eq : c = 1 := by omega
      subst ha_eq hb_eq hc_eq
      rfl
    have hsteps := (antihydraStepsResidual_iff n traj).mp ⟨d_seq, hres⟩
    have hrun : runAntihydraAccel n ahStart = some (traj n) :=
      (runAntihydraAccel_iff_trajectory n ahStart (traj n)).mpr ⟨traj, h0, rfl, hsteps⟩
    have hhalt : antihydraNext (traj n) = none :=
      (antihydraHaltPoly_eq_zero_iff (traj n)).mp hhalt_poly
    exact ⟨n, traj n, hrun, hhalt⟩

end DiophantineZQ
