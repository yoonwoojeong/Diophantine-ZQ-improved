# Diophantine-ZQ-improved

Formally verified theorems for Elliot Glazer’s Diophantine definition of $\mathbb{Z}$ in $\mathbb{Q}$ ([`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q)).

## Theorems

All theorems are fully proved in [`DiophantineZQ.lean`](DiophantineZQ.lean) and verified against [`Challenge.lean`](Challenge.lean):

### Theorem 1 (Lucas's Theorem for Submasks)
For any $a, b \in \mathbb{N}$:
$$\binom{b}{a} \equiv 1 \pmod 2 \iff a \mathbin{\&} b = a$$

### Theorem 2 (Carry-Free Register Decoding)
Let $K < B$. For any execution history where register values $\rho(t) < K$ and step changes $\alpha(t), \gamma(t) \le 1$, the packed integer equation:
$$\sum_{t=0}^q \rho(t) B^t + B \sum_{t=0}^q \gamma(t) B^t = \text{init} + B \sum_{t=0}^q \rho(t) B^t + B \sum_{t=0}^q \alpha(t) B^t$$
uniquely determines:
1. Initial state: $\rho(0) = \text{init}$
2. Transition steps: $\rho(t+1) + \gamma(t) = \rho(t) + \alpha(t)$ for all $t < q$
3. Final state: $\gamma(q) = \rho(q) + \alpha(q)$

### Theorem 3 (Single-Digit Zero-Testing)
For any $r \le 2^c - 1$ and $z \in \{0, 1\}$:
$$r \mathbin{\&} ((2^c - 1)(1 - z)) = r \iff (z = 1 \implies r = 0)$$

### Theorem 4 (Stage 1 Lowers the Total $\mathbb{Q}$-Witness Count)
**Stage 1** changes Glazer's natural circuit in two ways:
- each `bitAnd(V_i, S_i, N_j)` is replaced by $V_i \preceq S_i$;
- each `bitAnd(K N_j, R_j + D, K F)` and its $N_j$ are replaced by $M_j + K Z_j = D + Z_j$ and $R_j \preceq M_j$, where $Z_j = \sum W_i$ over the sub states that test register $j$.

The total is counted the way Glazer's translator (`rational-circuit-translator.js`) allocates witnesses. Each explicit natural variable costs $5 + 140{,}604$, each `add` node $5 + 6$, each `mul` node $5 + 35{,}134$ and each `power` call $5 + 17{,}786{,}698$. The non-`precision` recipes add a fixed $739{,}068$.

| Circuit | Variables | `add` | `mul` | `power` | Total $\mathbb{Q}$ witnesses |
| :--- | ---: | ---: | ---: | ---: | ---: |
| Baseline (`precision-natural-polynomial.json`) | 54,056 | 125,327 | 98,382 | 15,845 | **292,890,231,904** |
| Stage 1 | 29,536 | 69,135 | 53,428 | 8,489 | **157,023,255,238** |

That saves $135{,}866{,}976{,}666$ witnesses ($-46.39\%$). The Lean theorems are:
- `glazer_totalQ`: the accounting reproduces Glazer's published count $292{,}890{,}231{,}904$.
- `stage1_delta_from_gadgets`: per-gadget sizes give the change $(-20(R+S),\ -(45R+46S),\ -(35R+37S),\ -6(R+S))$ for $R$ tested registers and $S$ sub states.
- `stage1_totalQ_add_savings` and `stage1_totalQ_lt`: for any circuit, Stage 1 lowers the total by exactly `stage1QSavings R S`, which is positive when $R + S > 0$.
- `glazer_stage1_totalQ`, `glazer_stage1_totalQ_lt` and `glazer_stage1_Q_savings`: for Glazer's machine ($R = 204$, $S = 1022$), the total is $157{,}023{,}255{,}238 < 292{,}890{,}231{,}904$.

**How the counts were obtained.** [`scripts/stage1_circuit.js`](scripts/stage1_circuit.js) builds the Stage 1 circuit by editing Glazer's pinned circuit, using the same hash-consed node rules as `integer-diophantine-compiler.js`. Two self-checks support the edit:
- `identity` mode rebuilds the pinned file node for node.
- `regen` mode regenerates all 2,829 `mask`/`bitAnd` gadgets with the emulated macros and gets identical counts.

[`scripts/q_witness_accounting.js`](scripts/q_witness_accounting.js) reads `ordinary-integer-definition.json` and confirms that the allocation rule reproduces the pinned `precision` recipe. It then counts the Stage 1 circuit.

**Scope.** This is a count of witnesses only. The multi-slot correctness of the Stage 1 circuit (that it defines the same set) is not proved. Theorems 2 and 3 cover only the decoding and a single slot.

## Verification

```bash
lake build DiophantineZQ Challenge
lake comparator
```

To reproduce the circuit counts behind Theorem 4 (Node.js 22+):

```bash
git clone --depth 1 https://github.com/elliotglazer/diophantine-z-q.git glazer
```

```bash
node --max-old-space-size=4096 scripts/stage1_circuit.js glazer/construction/precision-natural-polynomial.json stage1 stage1.json
```

```bash
node --max-old-space-size=6000 scripts/q_witness_accounting.js glazer/construction/ordinary-integer-definition.json glazer/construction/precision-natural-polynomial.json stage1.json
```
