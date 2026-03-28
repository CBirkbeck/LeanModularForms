# Plan: Shimura Theorem 3.20 — R_p ≅ ℤ[X₁,...,Xₙ]

## Statement
The p-local Hecke ring R_p^(n) is the polynomial ring over ℤ in n
algebraically independent generators T_k^(n) = T(1,...,1,p,...,p)
(with n-k ones and k p's), for k = 1,...,n.

## Proof Strategy (from Shimura pp. 59-60)

### Part 1: Surjectivity (weight induction)

Every element of R_p is a polynomial in T_1,...,T_n.

1. Define weight w(T(p^{e₁},...,p^{eₙ})) = e₁ + ... + eₙ
2. Base case: w = 0 means T(1,...,1) = identity
3. If e₁ > 0: use Prop 3.17 to write
   T(p^{e₁},...,p^{eₙ}) = T(p,...,p) · T(p^{e₁-1},...,p^{eₙ-1})
   reducing weight by n
4. If e₁ = 0: use ψ: R_p^(n) → R_p^(n-1) from Lemma 3.19
   By induction on n, ψ(X) is a polynomial in T_1^(n-1),...,T_{n-1}^(n-1)
   Then X - Y has smaller weight, proceed by weight induction

### Part 2: Algebraic Independence

The T_k are algebraically independent over ℤ.

1. If P(T_1,...,T_n) = 0, write P = Σ (T_n)^{l-k} P_k(T_1,...,T_{n-1})
2. T_n = T(p,...,p) is not a zero-divisor (Prop 3.17)
3. Apply ψ to get P_k(T_1^(n-1),...,T_{n-1}^(n-1)) = 0
4. By induction on n, P_k = 0

### Missing Infrastructure

| Component | Status | Difficulty |
|-----------|--------|------------|
| `ppowWeight` | ✅ Done | — |
| `T_gen_mem_R_p` | ✅ Done | — |
| `T_diag_scalar_mul` (Prop 3.17) | ✅ Done | — |
| `evalHom` | ✅ Done | — |
| Lemma 3.19 (ψ map) | ❌ Missing | High |
| ψ is surjective | ❌ Missing | Medium |
| Ker(ψ) = T_n · R_p | ❌ Missing | High |
| Weight induction step | ❌ Missing | Medium |
| T(p,...,p) not zero-divisor | ❌ Missing | Medium |
| Algebraic independence | ❌ Missing | High |

### Estimated effort: ~500 lines of new Lean code
