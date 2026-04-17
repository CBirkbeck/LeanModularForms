# Ticket Board: Shimura Prop 3.34

## Summary
- Total: 7 tickets (P334-A through G)
- Open: 7 | In Progress: 0 | Done: 0
- Parallel capacity: 1-2 workers at peak (mostly linear chain)

## Tickets

### [P334-A] Precise statement + matrix entry lemma
- **Status**: open
- **File**: `LeanModularForms/HeckeRIngs/GL2/Prop334.lean` (new)
- **Depends on**: none
- **Description**: Write the precise Lean statement of Gamma0MapUnits preservation. Prove the key matrix computation lemma:
  ```lean
  lemma matrix_conjugate_entry_11_mod (g h : Matrix (Fin 2) (Fin 2) ℤ) (N : ℕ) ...
  ```
  showing `(g⁻¹ h g)₁₁ · det(g) ≡ ad·δ (mod N)` for `g = [[a,b],[Nc,d]]` and `h = [[α,β],[Nγ,δ]]`.
- **Naming**: `Matrix.fin_two_conj_entry_11_mod_eq` or similar.
- **Generality**: work over ℤ throughout; state via `Matrix (Fin 2) (Fin 2) ℤ`.
- **Budget**: ~80 LOC.

### [P334-B] Good-prime case of Prop 3.34
- **Status**: open
- **File**: `Prop334.lean`
- **Depends on**: P334-A
- **Description**: Prove Gamma0MapUnits preservation when `gcd(det g, N) = 1`:
  ```lean
  lemma Gamma0MapUnits_preserved_of_detCoprime (g : (Gamma0_pair N).Δ)
      (h_det_coprime : Nat.Coprime (det g).natAbs N)
      (h : ↥(Gamma0 N)) (h_conj_mem : ... ∈ Γ₀(N)) : ...
  ```
- **Approach**: apply P334-A, note `det(g)` invertible mod N, derive `δ' ≡ δ (mod N)`.
- **Budget**: ~60 LOC.

### [P334-C] Bad-prime case of Prop 3.34
- **Status**: open (optional — may skip if good-prime suffices)
- **File**: `Prop334.lean`
- **Depends on**: P334-A
- **Description**: Prove preservation when `gcd(det g, N) > 1`. Uses: det of conjugate = 1, combined with Γ₀ structure, forces (1,1) ≡ δ mod N via determinant identity.
- **Budget**: ~100 LOC.
- **Alternative**: skip this case and restrict all downstream results to coprime-det D's. Since our target (heckeT_p for p ∤ N) has coprime det p ≠ 0 mod N, this suffices.

### [P334-D] Assemble full Prop 3.34
- **Status**: open
- **File**: `Prop334.lean`
- **Depends on**: P334-B (and optionally P334-C)
- **Description**: Package as a clean theorem:
  ```lean
  theorem Gamma0MapUnits_preserved_under_conjugation_of_detCoprime (g : (Gamma0_pair N).Δ)
      (h_det_coprime : ...) (h : ↥(Gamma0 N)) (h' : ↥(Gamma0 N))
      (h'_eq_conj : ...) : Gamma0MapUnits h' = Gamma0MapUnits h
  ```
- **Budget**: ~20 LOC.

### [P334-E] heckeSlash_gen preservation of modFormCharSpace
- **Status**: open
- **File**: `HeckeRingHomCharSpace_General.lean` (extend) or new file
- **Depends on**: P334-D
- **Description**: Prove:
  ```lean
  theorem heckeSlash_gen_preserves_modFormCharSpace (k χ D)
      (h_det_coprime : Nat.Coprime (det (rep D)).natAbs N)
      (f : modFormCharSpace k χ) :
      (packaged version of heckeSlash_gen D f) ∈ modFormCharSpace k χ
  ```
  Using Prop 3.34 to track χ through the permutation argument.
- **Budget**: ~150-200 LOC.

### [P334-F] heckeRingHomCharSpace N k χ for arbitrary χ (coprime-det restriction)
- **Status**: open
- **File**: `HeckeRingHomCharSpace_General.lean` or new file
- **Depends on**: P334-E
- **Description**: Build the ring hom from a suitable subring of 𝕋(Gamma0_pair N) (coprime-det elements) to End(modFormCharSpace k χ).
- **Budget**: ~200 LOC.

### [P334-G] Refactor heckeT_p_all_comm_distinct via ring hom
- **Status**: open
- **File**: new helper or in `HeckeT_n.lean` directly
- **Depends on**: P334-F
- **Description**: Rewrite `heckeT_p_all_comm_distinct` (currently 200+ lines at `HeckeT_n.lean:1071`) as a short corollary: char decomp + per-χ ring hom + mul_comm in 𝕋(Gamma0_pair N).
- **Target**: ~30-50 line proof replacing the 200-line manual one.
- **Budget**: ~100 LOC total (refactor + any supporting infrastructure).
