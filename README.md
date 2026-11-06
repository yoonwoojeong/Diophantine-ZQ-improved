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

## Verification

```bash
lake build DiophantineZQ Challenge
lake comparator
```
