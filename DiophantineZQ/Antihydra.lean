/-
  DiophantineZQ.Antihydra
  =======================
  Mathlib-backed formalization of the BB(6) Cryptid Antihydra
  (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`), following `google-deepmind/cryptids`,
  without assuming or attempting to establish its unresolved halting status:
  1. 6-state transition table `AntihydraTM` and 12-step initial transition from blank tape
     to `P(0, 3, 1)` (`antihydra_reaches_start_in_12_steps`).
  2. Accelerated 3-counter Collatz-like map `antihydraNext` on `AHState` (`P(a, b, c)`).
  3. 1-witness single-fold Diophantine representation (`antihydraStepPoly_iff_next`,
     `antihydraStepPoly_unique`) proving both witness existence and witness uniqueness.
  4. Complete trajectory Diophantine equivalence (`antihydra_halts_iff_diophantine`).
-/

import DiophantineZQ.SmallTM

namespace DiophantineZQ

/-! ## 1. The BB(6) Cryptid Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) -/

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

/-- From the blank tape `(0, 0, 0)`, Antihydra reaches `P(0, 3, 1)` (`q=5, L=7, R=3`) in 12 steps. -/
theorem antihydra_reaches_start_in_12_steps :
    runTM AntihydraTM 12 initConfig = some ⟨5, 7, 3⟩ := by
  decide

/-! ## 2. Cryptids Accelerated 3-Counter Map `antihydraNext` on `P(a, b, c)` -/

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

theorem antihydra_accel_step_1 : antihydraNext ⟨0, 3, 1⟩ = some ⟨0, 1, 4⟩ := rfl
theorem antihydra_accel_step_2 : antihydraNext ⟨0, 1, 4⟩ = some ⟨2, 7, 1⟩ := rfl
theorem antihydra_accel_step_3 : antihydraNext ⟨2, 7, 1⟩ = some ⟨2, 5, 4⟩ := rfl
theorem antihydra_accel_step_4 : antihydraNext ⟨2, 5, 4⟩ = some ⟨2, 3, 7⟩ := rfl
theorem antihydra_accel_step_5 : antihydraNext ⟨2, 3, 7⟩ = some ⟨2, 1, 10⟩ := rfl

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

/-! ## 3. Exact 1-Witness Single-Fold Representation of `antihydraNext` over ℕ -/

def antihydraHaltPoly (s : AHState) : ℤ :=
  sumSquaresInt [(s.a : ℤ) - 0, (s.b : ℤ) - 2]

theorem antihydraHaltPoly_eq_zero_iff (s : AHState) :
    antihydraHaltPoly s = 0 ↔ antihydraNext s = none := by
  unfold antihydraHaltPoly
  rw [sumSquaresInt_eq_zero_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  cases s with | mk a b c =>
  dsimp
  constructor
  · rintro ⟨ha, hb⟩
    have : a = 0 := by omega
    have : b = 2 := by omega
    subst_vars; rfl
  · intro hnone
    unfold antihydraNext at hnone; dsimp at hnone
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a' <;> contradiction
    · rcases a with _ | a' <;> contradiction
    · rcases a with _ | a'
      · exact ⟨rfl, rfl⟩
      · contradiction
    · rcases a with _ | a' <;> contradiction

/-- Encodes all 5 non-halting branches of `antihydraNext s = some s'` using a single
    uniquely determined natural witness `d : ℕ`. -/
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

private theorem antihydraStepPoly_zero_decode (s s' : AHState) (d : ℕ)
    (h : antihydraStepPoly s s' d = 0) :
    antihydraNext s = some s' ∧
    d = (if s.b = 0 then s.a - 1 else if s.b = 1 then 0 else if s.b = 2 then s.a - 1 else s.b - 3) := by
  unfold antihydraStepPoly at h
  cases s with | mk a b c =>
  cases s' with | mk a' b' c' =>
  dsimp at h ⊢
  rcases mul_eq_zero.mp h with h1234 | h5
  · rcases mul_eq_zero.mp h1234 with h123 | h4
    · rcases mul_eq_zero.mp h123 with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · rw [sumSquaresInt_eq_zero_iff] at h1
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1
          rcases h1 with ⟨ha, hb, hd, ha', hb', hc'⟩
          have : a = 0 := by omega
          have : b = 0 := by omega
          have : d = 0 := by omega
          have : a' = 0 := by omega
          have : b' = c + 3 := by omega
          have : c' = 1 := by omega
          subst_vars; exact ⟨rfl, rfl⟩
        · rw [sumSquaresInt_eq_zero_iff] at h2
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2
          rcases h2 with ⟨ha, hb, ha', hb', hc'⟩
          have : a = d + 1 := by omega
          have : b = 0 := by omega
          have : a' = 0 := by omega
          have : b' = d + c + 7 := by omega
          have : c' = 1 := by omega
          subst_vars; exact ⟨rfl, by simp⟩
      · rw [sumSquaresInt_eq_zero_iff] at h3
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h3
        rcases h3 with ⟨hb, hd, ha', hb', hc'⟩
        have : b = 1 := by omega
        have : d = 0 := by omega
        have : a' = a + 2 := by omega
        have : b' = c + 3 := by omega
        have : c' = 1 := by omega
        subst_vars
        refine ⟨by rcases a with _ | _ <;> rfl, rfl⟩
    · rw [sumSquaresInt_eq_zero_iff] at h4
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h4
      rcases h4 with ⟨ha, hb, ha', hb', hc'⟩
      have : a = d + 1 := by omega
      have : b = 2 := by omega
      have : a' = d := by omega
      have : b' = c + 4 := by omega
      have : c' = 1 := by omega
      subst_vars; exact ⟨rfl, by simp⟩
  · rw [sumSquaresInt_eq_zero_iff] at h5
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h5
    rcases h5 with ⟨hb, ha', hb', hc'⟩
    have : b = d + 3 := by omega
    have : a' = a := by omega
    have : b' = d + 1 := by omega
    have : c' = c + 3 := by omega
    subst_vars
    have h1 : ¬ (d + 3 = 1) := by omega
    have h2 : ¬ (d + 3 = 2) := by omega
    refine ⟨by rcases a' with _ | _ <;> rfl, by simp [h1, h2]⟩

theorem antihydraStepPoly_iff_next (s s' : AHState) :
    (∃ d : ℕ, antihydraStepPoly s s' d = 0) ↔
    antihydraNext s = some s' := by
  constructor
  · rintro ⟨d, h⟩
    exact (antihydraStepPoly_zero_decode s s' d h).1
  · intro hnext
    unfold antihydraStepPoly
    cases s with | mk a b c =>
    cases s' with | mk a' b' c' =>
    dsimp
    unfold antihydraNext at hnext; dsimp at hnext
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a'
      · simp at hnext; rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨0, ?_⟩
        have hbr1 : sumSquaresInt [
            ((0 : ℕ) : ℤ) - 0, ((0 : ℕ) : ℤ) - 0, ((0 : ℕ) : ℤ) - 0,
            ((0 : ℕ) : ℤ) - 0, ((c + 3 : ℕ) : ℤ) - ((c : ℤ) + 3), ((1 : ℕ) : ℤ) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨rfl, rfl, rfl, rfl, by push_cast; ring, rfl⟩
        rw [hbr1]; simp
      · simp at hnext; rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨a', ?_⟩
        have hbr2 : sumSquaresInt [
            ((a' + 1 : ℕ) : ℤ) - ((a' : ℤ) + 1), ((0 : ℕ) : ℤ) - 0, ((0 : ℕ) : ℤ) - 0,
            ((a' + c + 7 : ℕ) : ℤ) - ((a' : ℤ) + (c : ℤ) + 7), ((1 : ℕ) : ℤ) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨by push_cast; ring, rfl, rfl, by push_cast; ring, rfl⟩
        rw [hbr2]; simp
    · simp at hnext; rcases hnext with ⟨rfl, rfl, rfl⟩
      refine ⟨0, ?_⟩
      have hbr3 : sumSquaresInt [
          ((1 : ℕ) : ℤ) - 1, ((0 : ℕ) : ℤ) - 0, ((a + 2 : ℕ) : ℤ) - ((a : ℤ) + 2),
          ((c + 3 : ℕ) : ℤ) - ((c : ℤ) + 3), ((1 : ℕ) : ℤ) - 1
        ] = 0 := by
        rw [sumSquaresInt_eq_zero_iff]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨rfl, rfl, by push_cast; ring, by push_cast; ring, rfl⟩
      rw [hbr3]; simp
    · rcases a with _ | a'
      · contradiction
      · simp at hnext; rcases hnext with ⟨rfl, rfl, rfl⟩
        refine ⟨a', ?_⟩
        have hbr4 : sumSquaresInt [
            ((a' + 1 : ℕ) : ℤ) - ((a' : ℤ) + 1), ((2 : ℕ) : ℤ) - 2, (a' : ℤ) - (a' : ℤ),
            ((c + 4 : ℕ) : ℤ) - ((c : ℤ) + 4), ((1 : ℕ) : ℤ) - 1
          ] = 0 := by
          rw [sumSquaresInt_eq_zero_iff]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨by push_cast; ring, rfl, by ring, by push_cast; ring, rfl⟩
        rw [hbr4]; simp
    · simp at hnext; rcases hnext with ⟨rfl, rfl, rfl⟩
      refine ⟨b', ?_⟩
      have hbr5 : sumSquaresInt [
          ((b' + 3 : ℕ) : ℤ) - ((b' : ℤ) + 3), (a : ℤ) - (a : ℤ),
          ((b' + 1 : ℕ) : ℤ) - ((b' : ℤ) + 1), ((c + 3 : ℕ) : ℤ) - ((c : ℤ) + 3)
        ] = 0 := by
        rw [sumSquaresInt_eq_zero_iff]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨by push_cast; ring, by ring, by push_cast; ring, by push_cast; ring⟩
      rw [hbr5]; simp

/-- Single-fold witness uniqueness for `antihydraStepPoly`: for any `(s, s')`, at most one
    natural witness `d : ℕ` satisfies `antihydraStepPoly s s' d = 0`. -/
theorem antihydraStepPoly_unique (s s' : AHState) (d₁ d₂ : ℕ)
    (h₁ : antihydraStepPoly s s' d₁ = 0)
    (h₂ : antihydraStepPoly s s' d₂ = 0) :
    d₁ = d₂ := by
  have hd₁ := (antihydraStepPoly_zero_decode s s' d₁ h₁).2
  have hd₂ := (antihydraStepPoly_zero_decode s s' d₂ h₂).2
  rw [hd₁, hd₂]

/-! ## 4. Full Trajectory Diophantine Equivalence for Antihydra -/

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

theorem antihydraStepsResidual_iff (n : ℕ) (traj : ℕ → AHState) :
    (∃ d_seq : ℕ → ℕ, antihydraStepsResidual n traj d_seq = 0) ↔
      (∀ t, t < n → antihydraNext (traj t) = some (traj (t + 1))) := by
  induction n generalizing traj with
  | zero => simp [antihydraStepsResidual]
  | succ m ih =>
    unfold antihydraStepsResidual
    constructor
    · rintro ⟨d_seq, h⟩
      rw [sumSquaresInt_eq_zero_iff] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
      rcases h with ⟨h0, hrest⟩
      have hstep0 := (antihydraStepPoly_iff_next (traj 0) (traj 1)).mp ⟨d_seq 0, h0⟩
      have hsteps := (ih (fun t => traj (t + 1))).mp ⟨fun t => d_seq (t + 1), hrest⟩
      intro t ht
      cases t with
      | zero => exact hstep0
      | succ k => exact hsteps k (Nat.lt_of_succ_lt_succ ht)
    · intro h
      obtain ⟨d0, hd0⟩ := (antihydraStepPoly_iff_next (traj 0) (traj 1)).mpr (h 0 (Nat.zero_lt_succ m))
      obtain ⟨d_tail, htail⟩ := (ih (fun t => traj (t + 1))).mpr (fun t ht => h (t + 1) (Nat.succ_lt_succ ht))
      refine ⟨fun t => match t with | 0 => d0 | t + 1 => d_tail t, ?_⟩
      rw [sumSquaresInt_eq_zero_iff]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hd0, htail⟩

theorem runAntihydraAccel_iff_trajectory (n : ℕ) (s₀ s_f : AHState) :
    runAntihydraAccel n s₀ = some s_f ↔
      ∃ traj : ℕ → AHState,
        traj 0 = s₀ ∧ traj n = s_f ∧
        (∀ t, t < n → antihydraNext (traj t) = some (traj (t + 1))) := by
  induction n generalizing s₀ with
  | zero =>
    unfold runAntihydraAccel
    exact ⟨fun h => by injection h with h_eq; subst h_eq; exact ⟨fun _ => s₀, rfl, rfl, fun _ ht => by omega⟩,
           by rintro ⟨traj, h0, hn, _⟩; subst h0 hn; rfl⟩
  | succ m ih =>
    unfold runAntihydraAccel
    constructor
    · intro h
      cases hnext : antihydraNext s₀ with
      | none => rw [hnext] at h; contradiction
      | some s₁ =>
        rw [hnext] at h
        obtain ⟨traj_tail, h0, hm, hsteps⟩ := (ih s₁).mp h
        refine ⟨fun t => match t with | 0 => s₀ | t + 1 => traj_tail t, rfl, hm, ?_⟩
        intro t ht
        cases t with
        | zero => dsimp; rw [h0]; exact hnext
        | succ k => exact hsteps k (Nat.lt_of_succ_lt_succ ht)
    · rintro ⟨traj, h0, hn, hsteps⟩
      have hstep0 : antihydraNext s₀ = some (traj 1) := by rw [← h0]; exact hsteps 0 (Nat.zero_lt_succ m)
      rw [hstep0]
      exact (ih (traj 1)).mpr ⟨fun t => traj (t + 1), rfl, hn, fun t ht => hsteps (t + 1) (Nat.succ_lt_succ ht)⟩

/-- Constructive Diophantine equivalence for `AntihydraCollatzHalts` without assuming
    or resolving Antihydra's open halting problem. -/
theorem antihydra_halts_iff_diophantine :
    AntihydraCollatzHalts ↔
      ∃ (n : ℕ) (traj : ℕ → AHState) (d_seq : ℕ → ℕ),
        antihydraTrajectoryPoly n traj d_seq = 0 := by
  unfold AntihydraCollatzHalts AntihydraCollatzHaltsIn antihydraTrajectoryPoly
  constructor
  · rintro ⟨n, s_f, hrun, hhalt⟩
    obtain ⟨traj, h0, hn, hsteps⟩ := (runAntihydraAccel_iff_trajectory n ahStart s_f).mp hrun
    obtain ⟨d_seq, hres⟩ := (antihydraStepsResidual_iff n traj).mpr hsteps
    have hhalt_poly : antihydraHaltPoly (traj n) = 0 := by
      rw [hn]; exact (antihydraHaltPoly_eq_zero_iff s_f).mpr hhalt
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
      rw [htraj0] at ha0 hb0 hc0; dsimp at ha0 hb0 hc0; unfold ahStart
      have : a = 0 := by omega
      have : b = 3 := by omega
      have : c = 1 := by omega
      subst_vars; rfl
    have hsteps := (antihydraStepsResidual_iff n traj).mp ⟨d_seq, hres⟩
    have hrun := (runAntihydraAccel_iff_trajectory n ahStart (traj n)).mpr ⟨traj, h0, rfl, hsteps⟩
    have hhalt := (antihydraHaltPoly_eq_zero_iff (traj n)).mp hhalt_poly
    exact ⟨n, traj n, hrun, hhalt⟩

end DiophantineZQ
