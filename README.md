# Diophantine-ZQ-improved

Formally verified mathematical proofs checking individual component lemmas from Elliot Glazer's construction ([`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q)).

## Proven Statements

The following statements are fully proved in [`DiophantineZQ.lean`](DiophantineZQ.lean) and verified against [`Challenge.lean`](Challenge.lean) with no unproven steps (`sorry`):

1. **Lucas's Theorem for Bitwise Submasks (`choose_odd_iff_land_eq`, `mask_iff_land_eq`)**:
   For all natural numbers $a$ and $b$, $\binom{b}{a}$ is odd if and only if $a \mathbin{\&} b = a$.

2. **Carry-Free History Decoding (`packed_register_decode`)**:
   For integers encoded in base $B$ with digits strictly less than $K < B$, the equation:
   $$R + B \cdot C = \text{init} + B \cdot R + B \cdot A$$
   uniquely recovers the initial value $\rho_0 = \text{init}$, every transition $\rho_{t+1} + \gamma_t = \rho_t + \alpha_t$, and the final state.

3. **Single-Digit Zero Test (`complement_mask_iff_zero_test`)**:
   For any single digit $r \le 2^c - 1$ and indicator $z \in \{0, 1\}$:
   $$r \mathbin{\&} ((2^c - 1)(1 - z)) = r \iff (z = 1 \implies r = 0)$$

4. **Single-Digit Branch Deduction (`single_slot_branch_correct`)**:
   Under the single-digit zero test and the transition equation $r' + v = r$ with state decomposition $s = v + z$, the values of $v$ and $z$ are uniquely forced to the correct branch.

5. **Structural Operation Formulas (`stage1_power_savings`, `glazer_baseline_power_calls`, `glazer_stage1_power_calls`)**:
   Exact arithmetic formulas for the baseline power count ($15,845$) and the single-test formula ($8,489$).

## How to Verify

```bash
lake build DiophantineZQ Challenge
lake comparator
```
