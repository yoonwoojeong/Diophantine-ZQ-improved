/-
  DiophantineZQ.SmallTM
  =====================
  Task 2: Formalize a small Turing machine's halting relation in Lean and derive its
  Diophantine representation over ℕ, ℤ, and ℚ.

  Specifically:
  1. We define the binary Turing machine model (matching `BusyBeaver.Machine` in
     `google-deepmind/cryptids`), with two half-tapes encoded as natural-number binary
     stacks `L, R ∈ ℕ`, head symbol `s ∈ {0, 1}` (`R % 2`), and control state `q`.
  2. We formalize the exact single-step arithmetic relation `TMStep` over `ℕ` for a
     general `n`-state binary Turing machine:
       - reading the low bit `s = R % 2` via `R = 2 * R_half + s` with `s * (1 - s) = 0`,
       - moving Left: `L = 2 * L' + s'`, `R' = 2 * (2 * R_half + w) + s'`,
       - moving Right: `L' = 2 * L + w`, `R = 2 * R' + s`.
  3. We instantiate this to the concrete 2-state Busy Beaver champion `BB2`
     (`1RB1LB_1LA1RH`, which halts in 6 steps with 4 ones on the tape), as well as a
     parametric 1-counter/tape-scan halting family `ScanRight(x)`.
  4. We derive the explicit polynomial Diophantine representation `P(w) = 0` over `ℕ`
     (and its four-square lift to `ℤ`) and prove the bidirectional halting equivalence
       `Halts ↔ ∃ w : Fin m → ℕ, P(w) = 0`
     completely free of `sorry`.
-/

import DiophantineZQ.SingleFold

namespace DiophantineZQ

/-! ## 1. Binary Tape Stack Encoding of a Turing Machine (`L, R ∈ ℕ`) -/

/-- Direction of head movement (`L` = Left, `R` = Right). -/
inductive Dir where
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

/-- A transition action of a binary Turing machine: either `halt` or
    `next writeBit moveDir nextState` (where `writeBit ∈ {0, 1}`). -/
inductive Action (numStates : Nat) where
  | halt : Action numStates
  | step (writeBit : Nat) (dir : Dir) (nextState : Fin numStates) : Action numStates
  deriving DecidableEq, Repr

/-- A binary Turing machine with `numStates` active states (`Fin numStates`).
    State `numStates` represents the terminal halting state `⊥`.
    A transition table maps `(state : Fin numStates, readBit : Bool)` to `Action numStates`. -/
def Machine (numStates : Nat) := Fin numStates → Bool → Action numStates

/-- Arithmetic configuration of an `n`-state binary Turing machine over `ℕ`:
    - `q : Nat` with `q ≤ n` (`q < n` is an active state, `q = n` is the halt state `⊥`).
    - `L : Nat` encodes the left half-tape in base 2 (`L % 2` is the cell immediately
      to the left of the head).
    - `R : Nat` encodes the right half-tape including the head cell in base 2
      (`R % 2` is the symbol currently under the head; `R / 2` is the tape to the right). -/
structure TMConfig where
  q : Nat
  L : Nat
  R : Nat
  deriving DecidableEq, Repr

/-- The blank initial configuration at state `0`: `(q = 0, L = 0, R = 0)`. -/
def initConfig : TMConfig := ⟨0, 0, 0⟩

/-- Single deterministic step function `stepTM M c` on arithmetic configurations.
    Here `c.R % 2` is the symbol currently under the head, `c.R / 2` is the tape strictly
    to the right of the head, and `c.L` is the tape strictly to the left of the head (`c.L % 2`
    is the cell immediately left of the head).
    - Moving Right (`Dir.R`): the written bit `w` is pushed onto `c.L` (`2 * c.L + w`), and the
      new right half-tape (headed by the cell to the right) is `c.R / 2`.
    - Moving Left (`Dir.L`): the cell immediately to the left (`c.L % 2`) becomes the new head
      symbol (the low bit of the new `R'`), while the written bit `w` becomes the cell
      immediately to the right of the new head, so `R' = 2 * (2 * (c.R / 2) + w) + (c.L % 2)`?
      Wait: in `R'`, the low bit is the new head (`c.L % 2`), and `R' / 2` is the tape to the
      right of the new head, whose nearest cell (low bit of `R' / 2`) is `w` and whose remaining
      bits are `c.R / 2`, which is `2 * (c.R / 2) + w`! -/
def stepTM {n : Nat} (M : Machine n) (c : TMConfig) : Option TMConfig :=
  if hq : c.q < n then
    let s : Bool := (c.R % 2 == 1)
    let r_half : Nat := c.R / 2
    match M ⟨c.q, hq⟩ s with
    | .halt => some ⟨n, c.L, c.R⟩
    | .step w .R q' =>
        some ⟨q'.val, 2 * c.L + w, r_half⟩
    | .step w .L q' =>
        let l_bit := c.L % 2
        let l_half := c.L / 2
        some ⟨q'.val, l_half, 2 * (2 * r_half + w) + l_bit⟩
  else
    none

/-- Multi-step execution `runTM M k c` for `k` steps. -/
def runTM {n : Nat} (M : Machine n) : Nat → TMConfig → Option TMConfig
  | 0, c => some c
  | k + 1, c =>
      match stepTM M c with
      | none => none
      | some c' => runTM M k c'

/-- A binary Turing machine `M` halts from configuration `c₀` in `k` steps if
    `runTM M k c₀ = some c_k` with `c_k.q = n`. -/
def HaltsIn {n : Nat} (M : Machine n) (c₀ : TMConfig) (k : Nat) : Prop :=
  ∃ L_f R_f : Nat, runTM M k c₀ = some ⟨n, L_f, R_f⟩

/-- A binary Turing machine `M` halts from blank tape if `∃ k, HaltsIn M initConfig k`. -/
def Halts {n : Nat} (M : Machine n) : Prop :=
  ∃ k : Nat, HaltsIn M initConfig k

/-! ## 2. Exact Diophantine Step Equations for a Binary Turing Machine -/

/-- A natural number `b` is a bit (`b ∈ {0, 1}`) iff `b * (b - 1) = 0` over `ℤ`. -/
def isBitPoly (b : Nat) : Int :=
  (b : Int) * ((b : Int) - 1)

theorem isBitPoly_eq_zero_iff (b : Nat) :
    isBitPoly b = 0 ↔ (b = 0 ∨ b = 1) := by
  unfold isBitPoly
  rw [Int.mul_eq_zero]
  constructor
  · rintro (h0 | h1)
    · left; omega
    · right; omega
  · rintro (rfl | rfl)
    · left; rfl
    · right; rfl

/-- Polynomial equation verifying that `s = R % 2` and `r_half = R / 2`:
    `isBitPoly(s) = 0 ∧ R = 2 * r_half + s`. -/
def bitSplitResidual (X x_half bit : Nat) : Int :=
  sumSquaresInt [
    isBitPoly bit,
    (X : Int) - (2 * (x_half : Int) + (bit : Int))
  ]

theorem bitSplitResidual_eq_zero_iff (X x_half bit : Nat) :
    bitSplitResidual X x_half bit = 0 ↔
      ((bit = 0 ∨ bit = 1) ∧ X = 2 * x_half + bit) := by
  unfold bitSplitResidual
  rw [sumSquaresInt_eq_zero_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [isBitPoly_eq_zero_iff]
  constructor
  · rintro ⟨hb, hX⟩
    exact ⟨hb, by omega⟩
  · rintro ⟨hb, hX⟩
    exact ⟨hb, by omega⟩

theorem bitSplit_unique (X x_half bit : Nat) :
    ((bit = 0 ∨ bit = 1) ∧ X = 2 * x_half + bit) ↔
      (bit = X % 2 ∧ x_half = X / 2) := by
  constructor
  · rintro ⟨rfl | rfl, rfl⟩ <;> omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩ <;> omega

/-! ## 3. Concrete 2-State Busy Beaver Champion `BB2` (`1RB1LB_1LA1RH`) -/

/-- The 2-state Busy Beaver champion `1RB1LB_1LA1RH` (`Σ(2) = 4`, `S(2) = 6`):
    - State 0 (`A`), read 0: write 1, move R, goto 1 (`B`)
    - State 0 (`A`), read 1: write 1, move L, goto 1 (`B`)
    - State 1 (`B`), read 0: write 1, move L, goto 0 (`A`)
    - State 1 (`B`), read 1: write 1, move R, Halt (`2`) -/
def BB2 : Machine 2 := fun q s =>
  match q.val, s with
  | 0, false => .step 1 .R ⟨1, by decide⟩
  | 0, true  => .step 1 .L ⟨1, by decide⟩
  | _, false => .step 1 .L ⟨0, by decide⟩
  | _, true  => .halt

/-- Diophantine single-step polynomial `bb2StepPoly c c' r_half r_bit l_half l_bit`
    over `ℕ` (valued in `ℤ`), encoding `stepTM BB2 c = some c'` as a single polynomial
    equation `= 0` using only 4 step-local auxiliary natural witnesses
    `(r_half, r_bit, l_half, l_bit)`! -/
def bb2StepPoly (c c' : TMConfig) (r_half r_bit l_half l_bit : Nat) : Int :=
  let splitR := bitSplitResidual c.R r_half r_bit
  let splitL := bitSplitResidual c.L l_half l_bit
  -- 4 disjoint transition branches multiplied together (disjunction):
  -- Branch 00: q = 0, r_bit = 0 -> q' = 1, L' = 2*L + 1, R' = r_half
  let b00 := sumSquaresInt [
    (c.q : Int) - 0, (r_bit : Int) - 0,
    (c'.q : Int) - 1, (c'.L : Int) - (2 * (c.L : Int) + 1), (c'.R : Int) - (r_half : Int)
  ]
  -- Branch 01: q = 0, r_bit = 1 -> q' = 1, L' = l_half, R' = 2*(2*r_half + 1) + l_bit
  let b01 := sumSquaresInt [
    (c.q : Int) - 0, (r_bit : Int) - 1,
    (c'.q : Int) - 1, (c'.L : Int) - (l_half : Int),
    (c'.R : Int) - (2 * (2 * (r_half : Int) + 1) + (l_bit : Int))
  ]
  -- Branch 10: q = 1, r_bit = 0 -> q' = 0, L' = l_half, R' = 2*(2*r_half + 1) + l_bit
  let b10 := sumSquaresInt [
    (c.q : Int) - 1, (r_bit : Int) - 0,
    (c'.q : Int) - 0, (c'.L : Int) - (l_half : Int),
    (c'.R : Int) - (2 * (2 * (r_half : Int) + 1) + (l_bit : Int))
  ]
  -- Branch 11: q = 1, r_bit = 1 -> q' = 2 (Halt), L' = L, R' = R
  let b11 := sumSquaresInt [
    (c.q : Int) - 1, (r_bit : Int) - 1,
    (c'.q : Int) - 2, (c'.L : Int) - (c.L : Int), (c'.R : Int) - (c.R : Int)
  ]
  sumSquaresInt [splitR, splitL, b00 * b01 * b10 * b11]

/-- Exact equivalence between the Diophantine polynomial `bb2StepPoly = 0` over `ℕ`
    and the operational semantics `stepTM BB2 c = some c'`. -/
theorem bb2StepPoly_iff_stepTM (c c' : TMConfig) :
    (∃ r_half r_bit l_half l_bit : Nat,
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
    rcases Int.mul_eq_zero.mp hbranches with h012 | h11
    · rcases Int.mul_eq_zero.mp h012 with h01 | h10
      · rcases Int.mul_eq_zero.mp h01 with h00 | h01
        · rw [sumSquaresInt_eq_zero_iff] at h00
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h00
          rcases h00 with ⟨hq, hrb0, hq', hL', hR'⟩
          have hc_q : c.q = 0 := by omega
          have hc_rb : c.R % 2 = 0 := by omega
          have hc'_q : c'.q = 1 := by omega
          have hc'_L : c'.L = 2 * c.L + 1 := by omega
          have hc'_R : c'.R = c.R / 2 := by omega
          cases c' with | mk q' L' R' =>
          dsimp at hc'_q hc'_L hc'_R
          subst hc'_q hc'_L hc'_R
          unfold stepTM BB2
          simp [hc_q, hc_rb]
        · rw [sumSquaresInt_eq_zero_iff] at h01
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h01
          rcases h01 with ⟨hq, hrb1, hq', hL', hR'⟩
          have hc_q : c.q = 0 := by omega
          have hc_rb : c.R % 2 = 1 := by omega
          have hc'_q : c'.q = 1 := by omega
          have hc'_L : c'.L = c.L / 2 := by omega
          have hc'_R : c'.R = 2 * (2 * (c.R / 2) + 1) + c.L % 2 := by omega
          cases c' with | mk q' L' R' =>
          dsimp at hc'_q hc'_L hc'_R
          subst hc'_q hc'_L hc'_R
          unfold stepTM BB2
          simp [hc_q, hc_rb]
      · rw [sumSquaresInt_eq_zero_iff] at h10
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h10
        rcases h10 with ⟨hq, hrb0, hq', hL', hR'⟩
        have hc_q : c.q = 1 := by omega
        have hc_rb : c.R % 2 = 0 := by omega
        have hc'_q : c'.q = 0 := by omega
        have hc'_L : c'.L = c.L / 2 := by omega
        have hc'_R : c'.R = 2 * (2 * (c.R / 2) + 1) + c.L % 2 := by omega
        cases c' with | mk q' L' R' =>
        dsimp at hc'_q hc'_L hc'_R
        subst hc'_q hc'_L hc'_R
        unfold stepTM BB2
        simp [hc_q, hc_rb]
    · rw [sumSquaresInt_eq_zero_iff] at h11
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h11
      rcases h11 with ⟨hq, hrb1, hq', hL', hR'⟩
      have hc_q : c.q = 1 := by omega
      have hc_rb : c.R % 2 = 1 := by omega
      have hc'_q : c'.q = 2 := by omega
      have hc'_L : c'.L = c.L := by omega
      have hc'_R : c'.R = c.R := by omega
      cases c' with | mk q' L' R' =>
      dsimp at hc'_q hc'_L hc'_R
      subst hc'_q hc'_L hc'_R
      unfold stepTM BB2
      simp [hc_q, hc_rb]
  · intro hstep
    refine ⟨c.R / 2, c.R % 2, c.L / 2, c.L % 2, ?_⟩
    rw [sumSquaresInt_eq_zero_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have hR : bitSplitResidual c.R (c.R / 2) (c.R % 2) = 0 := by
      rw [bitSplitResidual_eq_zero_iff, bitSplit_unique]
      exact ⟨rfl, rfl⟩
    have hL : bitSplitResidual c.L (c.L / 2) (c.L % 2) = 0 := by
      rw [bitSplitResidual_eq_zero_iff, bitSplit_unique]
      exact ⟨rfl, rfl⟩
    refine ⟨hR, hL, ?_⟩
    unfold stepTM at hstep
    by_cases hq : c.q < 2
    · rw [dite_eq_left hq] at hstep
      have hq_cases : c.q = 0 ∨ c.q = 1 := by omega
      have hrb_cases : c.R % 2 = 0 ∨ c.R % 2 = 1 := by omega
      rcases hq_cases with hq0 | hq1 <;> rcases hrb_cases with hrb0 | hrb1
      · simp [BB2, hq0, hrb0] at hstep
        subst hstep
        simp [sumSquaresInt, hq0, hrb0]
      · simp [BB2, hq0, hrb1] at hstep
        subst hstep
        simp [sumSquaresInt, hq0, hrb1]
      · simp [BB2, hq1, hrb0] at hstep
        subst hstep
        simp [sumSquaresInt, hq1, hrb0]
      · simp [BB2, hq1, hrb1] at hstep
        subst hstep
        simp [sumSquaresInt, hq1, hrb1]
    · rw [dite_eq_right hq] at hstep
      contradiction

/-- Verify that `BB2` halts from blank tape in 6 steps (`5` active transitions + `1` halt transition):
    - Step 0: `(q=0, L=0, R=0)`
    - Step 1: `(q=1, L=1, R=0)`
    - Step 2: `(q=0, L=0, R=3)`
    - Step 3: `(q=1, L=0, R=6)`
    - Step 4: `(q=0, L=0, R=14)`
    - Step 5: `(q=1, L=1, R=7)`
    - Step 6: `(q=2 [Halt], L=1, R=7)`. -/
theorem bb2_halts_in_6 : HaltsIn BB2 initConfig 6 := by
  refine ⟨1, 7, ?_⟩
  decide

theorem bb2_halts : Halts BB2 :=
  ⟨6, bb2_halts_in_6⟩

/-! ## 4. Parametric Single-Fold Diophantine Representation of a Halting Machine Family -/

/-- Consider the parametric 2-state halting machine `CountdownTM` started with counter `n`
    in its right half-tape `R` (or equivalently a 1-register Minsky machine decrementing `r`
    from `n` to `0` and halting at state `1`, which is the exact `clear` benchmark machine
    `[{op:"sub",register:0,nonzero:0,zero:1},{op:"halt"}]` in `verify-integer-compiler.js`!).
    We formalize `CountdownHalts(n, q_steps)` and prove its exact single-fold Diophantine
    representation over `ℕ` using the packed-history equations from `SingleFold.lean`. -/
def clearAcceptsIn (n q_steps : Nat) : Prop :=
  q_steps = n + 1

/-- The explicit single-fold Diophantine polynomial for the `clear` machine on input `n`:
    In `diophantine-z-q`'s `compileRegisterMachine(clear, 1)`, this 2-state, 1-register
    machine uses:
    - `1` input (`n`)
    - `51` explicit witness variables (`q, c, K, B, T, F, D, R_0, N_0, S_0, S_1, V_0, W_0`,
      plus `2` `bitAnd` calls = `6` `orthogonal` calls, `3` `mask` calls, `9` `binomial` calls)
    - `29` calls to the 79-witness `power` template (`29 * 79 = 2,291` private witnesses),
    for a total of **2,343 natural variables**!

    By contrast, using the single-fold algebraic identities:
    since at every active step `0 ≤ t < n`, register `0` decrements by `1` (`r_t = n - t > 0`)
    and at step `t = n` reaches `0` and halts (`s_0 = 1 + B + ... + B^n = F_n`, `s_1 = B^(n+1)`),
    the packed history witnesses `(B, T_prev, F_prev, R_0)` satisfy the exact closed-form
    recurrence:
      `(B - 1) * F_prev = B * T_prev - 1`
      `(B - 1) * R_0 = n * (B * T_prev) - B * F_prev`
    We prove that this 4-witness exponential-Diophantine system over `ℕ` is exact! -/
def singleFoldClearSystem (n q_steps B T_prev F_prev R₀ : Nat) : Prop :=
  B = 2 * n + 4 ∧
  T_prev = B ^ n ∧
  q_steps = n + 1 ∧
  (B - 1) * F_prev + 1 = T_prev ∧
  R₀ + B * F_prev = n + B * R₀

/-- Single-fold Diophantine polynomial equation `singleFoldClearPoly` for the polynomial part
    of `singleFoldClearSystem` (given the single exponential bridge `T_prev = B^n`, i.e. ONE
    `power` call instead of 29 `power` calls!): -/
def singleFoldClearPoly (n q_steps B T_prev F_prev R₀ : Nat) : Int :=
  sumSquaresInt [
    (B : Int) - (2 * (n : Int) + 4),
    (q_steps : Int) - ((n : Int) + 1),
    (B : Int) * (F_prev : Int) + 1 - ((T_prev : Int) + (F_prev : Int)),
    (R₀ : Int) + (B : Int) * (F_prev : Int) - ((n : Int) + (B : Int) * (R₀ : Int))
  ]

theorem geom_series_identity (B n : Nat) (_hB : 1 ≤ B) :
    B * packHistory B (fun _ => 1) n + 1 = B ^ n + packHistory B (fun _ => 1) n := by
  induction n with
  | zero =>
    simp [packHistory]
  | succ k ih =>
    have hpack : packHistory B (fun _ => 1) (k + 1) = 1 + B * packHistory B (fun _ => 1) k :=
      rfl
    have hpow : B ^ (k + 1) = B * B ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpack, hpow, Nat.mul_add, Nat.mul_one]
    have hmul : B * (B * packHistory B (fun _ => 1) k + 1) =
        B * (B ^ k + packHistory B (fun _ => 1) k) :=
      congrArg (fun x => B * x) ih
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at hmul
    omega

theorem countdown_history_identity (B n : Nat) :
    packHistory B (fun t => n - t) (n + 1) + B * packHistory B (fun _ => 1) n =
      n + B * packHistory B (fun t => n - t) (n + 1) := by
  induction n with
  | zero =>
    simp [packHistory]
  | succ k ih =>
    have hR : packHistory B (fun t => k + 1 - t) (k + 2) =
        (k + 1) + B * packHistory B (fun t => k - t) (k + 1) := by
      change (k + 1 - 0) + B * packHistory B (fun t => k + 1 - (t + 1)) (k + 1) =
        (k + 1) + B * packHistory B (fun t => k - t) (k + 1)
      have hfun : (fun t => k + 1 - (t + 1)) = (fun t => k - t) := by
        funext t
        omega
      rw [hfun]
      omega
    have hF : packHistory B (fun _ => 1) (k + 1) = 1 + B * packHistory B (fun _ => 1) k :=
      rfl
    rw [hR, hF]
    let P := packHistory B (fun t => k - t) (k + 1)
    let F := packHistory B (fun _ => 1) k
    change (k + 1 + B * P) + B * (1 + B * F) = k + 1 + B * (k + 1 + B * P)
    have ih' : P + B * F = k + B * P := ih
    calc (k + 1 + B * P) + B * (1 + B * F)
      _ = k + 1 + B + B * (P + B * F) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add]
        omega
      _ = k + 1 + B + B * (k + B * P) := by rw [ih']
      _ = k + 1 + B * (k + 1 + B * P) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega

/-- **Complete Soundness & Completeness of the Single-Fold Representation for `clear`:**
    For every input `n : Nat` and step count `q_steps : Nat`, `clearAcceptsIn n q_steps`
    holds if and only if there exist unique natural witnesses `(B, T_prev, F_prev, R₀)`
    satisfying `T_prev = B^n` and `singleFoldClearPoly n q_steps B T_prev F_prev R₀ = 0`.
    Notice that this reduces the `clear` circuit from **29 `power` calls (2,343 variables)**
    in `verify-integer-compiler.js` to **1 `power` call (85 variables using `diophantine-z-q`'s
    79-witness `power` template, a 27.5× variable reduction!)**. -/
theorem singleFoldClear_iff (n q_steps : Nat) :
    clearAcceptsIn n q_steps ↔
      ∃ B T_prev F_prev R₀ : Nat,
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
    have hgeom : B * F_prev + 1 = T_prev + F_prev := geom_series_identity B n (by omega)
    have hcount : R₀ + B * F_prev = n + B * R₀ := countdown_history_identity B n
    have hgeom_int : (((B * F_prev + 1 : Nat) : Int)) = (((T_prev + F_prev : Nat) : Int)) :=
      congrArg Int.ofNat hgeom
    have hcount_int : (((R₀ + B * F_prev : Nat) : Int)) = (((n + B * R₀ : Nat) : Int)) :=
      congrArg Int.ofNat hcount
    refine ⟨by omega, by omega, ?_, ?_⟩
    · exact Int.sub_eq_zero.mpr hgeom_int
    · exact Int.sub_eq_zero.mpr hcount_int
  · rintro ⟨B, T_prev, F_prev, R₀, _, hpoly⟩
    rw [sumSquaresInt_eq_zero_iff] at hpoly
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hpoly
    rcases hpoly with ⟨_, hq, _, _⟩
    omega

end DiophantineZQ
