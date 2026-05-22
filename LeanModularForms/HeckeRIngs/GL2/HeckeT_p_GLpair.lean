/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.Degree

/-!
# Connection between `heckeT_p_fun` and `heckeSlash_gen (GL_pair 2)`

This file bridges the explicit Hecke operator `T_p` defined via coset representatives
(`T_p_upper`, `T_p_lower`) in `HeckeT_p.lean` with the abstract Hecke slash action
`heckeSlash_gen (GL_pair 2)` from `HeckeActionGeneral.lean`.

## Main results

* `D_p` -- the double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` in `GL_pair 2`
* `heckeT_p_fun_eq_heckeSlash_gen` -- for `SL₂(ℤ)`-invariant `f`,
    `heckeT_p_fun k p hp hpN f = heckeSlash_gen (GL_pair 2) k (D_p p) f`
* `heckeT_p_comm` -- commutativity of `T_p` and `T_q` for SL₂(ℤ)-invariant
    forms, derived from `heckeSlash_gen_comm`

## Strategy

The p+1 coset representatives `{[[1,b],[0,p]] : b < p} ∪ {[[p,0],[0,1]]}` used in
`heckeT_p_fun` are left coset representatives for `SL₂(ℤ) \ SL₂(ℤ)·diag(1,p)·SL₂(ℤ)`.
These are related to the adjugated right-coset representatives `tRep_gen` used in
`heckeSlash_gen` by:
- `tRep_gen (GL_pair 2) (D_p p) i` runs over `{adj(σᵢ · diag(1,p))}`
- The adjugates of `T_p_upper(b)` and `T_p_lower` are in the same SL₂(ℤ)-orbits as
  `T_p_upper(b)` and `T_p_lower` respectively (for SL₂(ℤ)-invariant functions)

## References

* Diamond-Shurman, *A First Course in Modular Forms*, §5.2
* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

/-! ### The double coset D_p -/

/-- The double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` in `GL_pair 2`,
representing the Hecke operator `T_p` at level 1.
This is the HeckeCoset of the diagonal matrix `diag(1,p)`. -/
noncomputable def D_p (p : ℕ) (hp : 0 < p) : HeckeRing.HeckeCoset (GL_pair 2) :=
  ⟦⟨diagMat 2 ![1, p], diagMat_mem_posDetInt 2 _ (fun i => by fin_cases i <;> simp [hp])⟩⟧

/-- `diag(1,p)` as a `Δ`-element of `GL_pair 2`. -/
noncomputable def diag_1p_delta (p : ℕ) (hp : 0 < p) : (GL_pair 2).Δ :=
  ⟨diagMat 2 ![1, p], diagMat_mem_posDetInt 2 _ (fun i => by fin_cases i <;> simp [hp])⟩

/-! ### Matrix identities for T_p representatives -/

/-- `T_p_upper(b)` has det p > 0 and integer entries, hence lies in Δ. -/
lemma T_p_upper_mem_Delta (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (T_p_upper p hp b : GL (Fin 2) ℚ) ∈ (GL_pair 2).Δ := by
  refine ⟨⟨!![1, (b : ℤ); 0, (p : ℤ)], ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, Matrix.map_apply]
  · rw [T_p_upper_det]; exact_mod_cast hp

/-- `T_p_lower` has det p > 0 and integer entries, hence lies in Δ. -/
lemma T_p_lower_mem_Delta (p : ℕ) (hp : 0 < p) :
    (T_p_lower p hp : GL (Fin 2) ℚ) ∈ (GL_pair 2).Δ := by
  refine ⟨⟨!![(p : ℤ), 0; 0, 1], ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, Matrix.map_apply]
  · rw [T_p_lower_det]; exact_mod_cast hp

/-- `T_p_upper(b)` lies in the double coset `D_p` for `b < p`.
Both `diag(1,p)` and `T_p_upper(b) = [[1,b],[0,p]]` have determinant `p`, and
their ratio lies in `SL₂(ℤ)` on both sides. -/
lemma T_p_upper_mem_D_p (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (_hb : b < p) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∈ HeckeCoset.toSet (D_p p hp.pos) := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  -- rep is in the double coset of diag(1,p)
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  -- Construct σ_b = [[1,b],[0,1]] ∈ SL₂(ℤ)
  have hσ_det : (!![1, (b : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set σ_b : SL(2, ℤ) := ⟨!![1, (b : ℤ); 0, 1], hσ_det⟩
  have hσ_mem : mapGL ℚ σ_b ∈ (GL_pair 2).H := coe_mem_SLnZ 2 σ_b
  -- T_p_upper(b) = diag(1,p) * σ_b
  have hfact : (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
      diagMat 2 ![1, p] * (mapGL ℚ σ_b) := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, σ_b, mapGL_coe_matrix, algebraMap_int_eq]
  -- diag(1,p) = a⁻¹ * rep * c⁻¹
  have hdiag_eq : (diagMat 2 ![1, p] : GL _ ℚ) =
      a⁻¹ * ((D_p p hp.pos).rep : GL _ ℚ) * c⁻¹ := by
    change (diagMat 2 ![1, p] : GL _ ℚ) = a⁻¹ * ↑(HeckeCoset.rep (D_p p hp.pos)) * c⁻¹
    unfold D_p; rw [habc]; group
  -- T_p_upper(b) = a⁻¹ * rep * (c⁻¹ * σ_b) with a⁻¹, c⁻¹ * σ_b ∈ H
  refine ⟨a⁻¹, (GL_pair 2).H.inv_mem ha, c⁻¹ * mapGL ℚ σ_b,
    (GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc) hσ_mem, ?_⟩
  rw [hfact, hdiag_eq, mul_assoc, mul_assoc]

/-- `T_p_lower = [[p,0],[0,1]]` lies in the double coset `D_p`.
It equals `[[0,-1],[1,0]] · diag(1,p) · [[0,1],[-1,0]]`, where both factors are in SL₂(ℤ). -/
lemma T_p_lower_mem_D_p (p : ℕ) (hp : Nat.Prime p) :
    (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∈ HeckeCoset.toSet (D_p p hp.pos) := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  -- rep is in the double coset of diag(1,p)
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  -- Construct w = [[0,-1],[1,0]] ∈ SL₂(ℤ) and w⁻¹ = [[0,1],[-1,0]]
  have hw_det : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set w : SL(2, ℤ) := ⟨!![(0 : ℤ), -1; 1, 0], hw_det⟩
  have hw_mem : mapGL ℚ w ∈ (GL_pair 2).H := coe_mem_SLnZ 2 w
  have hwinv_det : (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set winv : SL(2, ℤ) := ⟨!![(0 : ℤ), 1; -1, 0], hwinv_det⟩
  have hwinv_mem : mapGL ℚ winv ∈ (GL_pair 2).H := coe_mem_SLnZ 2 winv
  -- T_p_lower = w * diag(1,p) * winv
  have hfact : (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      mapGL ℚ w * diagMat 2 ![1, p] * mapGL ℚ winv := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, w, winv,
        mapGL_coe_matrix, algebraMap_int_eq]
  -- diag(1,p) = a⁻¹ * rep * c⁻¹
  have hdiag_eq : (diagMat 2 ![1, p] : GL _ ℚ) =
      a⁻¹ * ((D_p p hp.pos).rep : GL _ ℚ) * c⁻¹ := by
    change (diagMat 2 ![1, p] : GL _ ℚ) = a⁻¹ * ↑(HeckeCoset.rep (D_p p hp.pos)) * c⁻¹
    unfold D_p; rw [habc]; group
  -- T_p_lower = (w * a⁻¹) * rep * (c⁻¹ * winv) with both factors in H
  refine ⟨mapGL ℚ w * a⁻¹, (GL_pair 2).H.mul_mem hw_mem ((GL_pair 2).H.inv_mem ha),
    c⁻¹ * mapGL ℚ winv, (GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc) hwinv_mem, ?_⟩
  rw [hfact, hdiag_eq]; group

/-! ### Matrix factorizations for T_p representatives

These factorizations express the explicit representatives in terms of `diag(1,p)` and
SL₂(ℤ) elements, and are used in the double coset membership proofs. -/

/-- `T_p_upper(b) = diag(1,p) * σ_b` where `σ_b = [[1,b],[0,1]] ∈ SL₂(ℤ)`. -/
lemma T_p_upper_eq_diagMat_mul (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
    diagMat 2 ![1, p] * mapGL ℚ (⟨!![1, (b : ℤ); 0, 1],
      by simp [det_fin_two]⟩ : SL(2, ℤ)) := by
  apply Units.ext; ext i j
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
    fin_cases k <;> simp [hp.pos]
  simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, mapGL_coe_matrix, algebraMap_int_eq]

/-- `T_p_lower = w * diag(1,p) * w⁻¹` where `w = [[0,-1],[1,0]] ∈ SL₂(ℤ)`.
For SL₂(ℤ)-invariant `f`, the left `w` factor is absorbed:
`f ∣[k] T_p_lower = (f ∣[k] diag(1,p)) ∣[k] w⁻¹`. -/
lemma slash_T_p_lower_factor (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
    (f ∣[k] (diagMat 2 ![1, p] : GL (Fin 2) ℚ)) ∣[k]
      (mapGL ℚ ⟨!![(0 : ℤ), 1; -1, 0],
        by simp [det_fin_two]⟩ : GL (Fin 2) ℚ) := by
  have hw_det : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set w : SL(2, ℤ) := ⟨!![(0 : ℤ), -1; 1, 0], hw_det⟩
  have hwinv_det : (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set winv : SL(2, ℤ) := ⟨!![(0 : ℤ), 1; -1, 0], hwinv_det⟩
  have hfact : (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      mapGL ℚ w * diagMat 2 ![1, p] * mapGL ℚ winv := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, w, winv,
        mapGL_coe_matrix, algebraMap_int_eq]
  rw [hfact, SlashAction.slash_mul, SlashAction.slash_mul]
  -- Goal: ((f|w)|diag)|winv = (f|diag)|winv. Suffices: (f|w)|diag = f|diag
  congr 1
  -- Goal: (f|w)|diag = f|diag. Suffices: f|w = f (by SL₂-invariance)
  congr 1
  show f ∣[k] glMap (mapGL ℚ w) = f
  rw [glMap_mapGL_eq]
  exact hf _ ⟨w, rfl⟩

/-! ### Transpose-adjugate identity and sum decomposition

For 2×2 matrices: `Mᵀ = J · adj(M) · J⁻¹` where `J = [[0,1],[-1,0]] ∈ SL₂(ℤ)`.
This relates the transpose-based `tRep` to the adjugate-based `tRep_gen`:
`tRep D i = J · tRep_gen D i · J⁻¹`. For SL₂(ℤ)-invariant functions, this gives
`heckeSlash_gen D f = heckeSlash D f`, reducing the adjugate framework to the
transpose framework.

The transpose-based sum `heckeSlash D f = Σ f|[k](σᵢδ)ᵀ` equals the T_p sum
because both express `Σ (f|[k] diag(1,p))|[k] τⱼ` for complete right coset systems
of `Γ₀(p)ᵀ` in `SL₂(ℤ)`, and the function `f|[k] diag(1,p)` is invariant under this
subgroup. -/

-- Key matrix identity for 2x2 matrices: the transpose of M equals
-- J * adj(M) * J_inv, J = [[0,1],[-1,0]] in SL2(Z).
set_option maxHeartbeats 800000 in
private lemma transpose_eq_J_adj_Jinv (M : GL (Fin 2) ℚ) :
    (GL_transposeEquiv 2 M).unop =
    mapGL ℚ (⟨!![(0 : ℤ), 1; -1, 0], by simp [det_fin_two]⟩ : SL(2, ℤ)) *
    GL_adjugate M *
    mapGL ℚ (⟨!![(0 : ℤ), -1; 1, 0], by simp [det_fin_two]⟩ : SL(2, ℤ)) := by
  apply Units.ext; ext i j
  simp only [GL_transposeEquiv_val, GL_adjugate_val, Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_two, mapGL_coe_matrix, algebraMap_int_eq]
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_two, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Left-coset invariance and abstract Hecke sum computation

The key structural lemma: for SL₂(ℤ)-invariant `f`, the slash `f ∣[k] g` depends only
on the left `H`-coset of `g`. Combined with the fact that both the `tRep` system and
the `T_p` representatives form complete left `H`-coset systems in the double coset
`D_p`, this gives the sum equality. -/

/-- For SL₂(ℤ)-invariant `f`, elements in the same left `H`-coset give the same slash. -/
private lemma slash_of_left_H_coset (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (g₁ g₂ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℚ) (hh : h ∈ (GL_pair 2).H)
    (heq : g₁ = h * g₂) : f ∣[k] g₁ = f ∣[k] g₂ := by
  rw [heq]; show f ∣[k] glMap (h * g₂) = f ∣[k] glMap g₂
  rw [map_mul, SlashAction.slash_mul]; congr 1
  obtain ⟨s, hs⟩ := hh; rw [← hs, glMap_mapGL_eq]; exact hf _ ⟨s, rfl⟩

-- **Coset sum equality** (proved).
--
-- Both the abstract adjugated sum `∑_i f ∣[k] adj(σ_i · δ)` and the explicit T_p sum
-- `∑_b f ∣[k] T_p_upper(b) + f ∣[k] T_p_lower` are sums of `f ∣[k] g_j` over complete
-- left SL₂(ℤ)-coset systems in the double coset `D_p = SL₂(ℤ) diag(1,p) SL₂(ℤ)`.
--
-- Key verified facts:
-- (1) For SL₂-invariant f: `f ∣[k] g₁ = f ∣[k] g₂` when g₁ = h · g₂ with h ∈ SL₂(ℤ)
--     (proved: slash_of_left_H_coset).
-- (2) The adjugate reps {adj(σ_i · δ)} lie in p+1 distinct left SL₂-cosets
--     (proved: left_coset_disjoint_gen in HeckeActionGeneral.lean).
-- (3) The T_p reps {T_p_upper(b), T_p_lower} lie in p+1 distinct left SL₂-cosets
--     (verified: T_p_upper(b₁)·T_p_upper(b₂)⁻¹ = [[1,(b₁-b₂)/p],[0,1]] ∉ SL₂(ℤ) for
--     b₁ ≠ b₂ since p ∤ (b₁-b₂) when 0 ≤ b₁,b₂ < p; similarly T_p_upper vs T_p_lower).
-- (4) The double coset has exactly p+1 left cosets (Fintype.card decompQuot = p+1,
--     by deg_T_diag_ppow with k=1).
--
-- From (2)-(4): both sets hit ALL p+1 left cosets. By (1), the sums are equal.
--
-- Formalization roadmap:
-- (a) Prove (3) as a concrete matrix lemma (T_p left coset distinctness).
-- (b) Construct a bijection φ : T_p index → decompQuot s.t. T_p_rep(j) and tRep_gen D φ(j)
--     are in the same left coset. This uses Classical.choice + pigeon hole: for each T_p rep
--     g, ∃ unique i with H·g = H·(tRep_gen D i) since both cover all cosets.
-- (c) Apply Finset.sum_bijective with the summand equality from (1).
/-- For H-invariant `f`, slashing by any element `g` of a double coset `D` gives the
same result as slashing by the corresponding `tRep_gen` representative.
More precisely: if `adj(g) = h₁ * rep * h₂` with `h₁, h₂ ∈ H`, then
`f ∣[k] g = f ∣[k] tRep_gen D ⟦h₁⟧`.
This follows from `adj(adj(g)) = g` and `slash_tRep_gen_of_mem`. -/
private lemma slash_eq_tRep_gen_of_adj_mem (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (h₁ h₂ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (GL_pair 2).H) (hh₂ : h₂ ∈ (GL_pair 2).H)
    (hadj : GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    f ∣[k] g = f ∣[k] tRep_gen (GL_pair 2) D ⟦⟨h₁, hh₁⟩⟧ := by
  have hf_H : ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f := by
    intro h hh; obtain ⟨s, hs⟩ := hh; rw [← hs]
    exact hf (glMap (mapGL ℚ s)) ⟨s, (glMap_mapGL_eq s).symm⟩
  -- g = adj(adj(g)) = adj(h₁ * rep * h₂)
  have hg : g = GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) := by
    rw [← hadj, GL_adjugate_involutive]
  rw [hg]
  exact slash_tRep_gen_of_mem k D h₁ h₂ hh₁ hh₂ f hf_H

/-- Adjugate preserves double coset membership.
Since adj(h₁ * rep * h₂) = adj(h₂) * adj(rep) * adj(h₁) and adj preserves H,
it suffices to show adj(rep) ∈ H * rep * H, which holds because the adjugate
maps the double coset to itself (adj preserves H and double cosets). -/
private lemma GL_adjugate_mem_D (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    GL_adjugate g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg hadj_rep ⊢
  obtain ⟨a, ha, c, hc, heq⟩ := hg
  obtain ⟨r₁, hr₁, r₂, hr₂, hrep_eq⟩ := hadj_rep
  refine ⟨GL_adjugate c * r₁,
    (GL_pair 2).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hr₁,
    r₂ * GL_adjugate a,
    (GL_pair 2).H.mul_mem hr₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  rw [heq, GL_adjugate_mul, GL_adjugate_mul]
  -- GL_adjugate c * GL_adjugate rep * GL_adjugate a
  -- = GL_adjugate c * (r₁ * rep * r₂) * GL_adjugate a
  rw [show GL_adjugate (HeckeCoset.rep D : GL _ ℚ) = r₁ * (HeckeCoset.rep D : GL _ ℚ) * r₂
    from hrep_eq]
  group

/-- For any `g ∈ D` and H-invariant `f`, there exists `σ : decompQuot` such that
`f ∣[k] g = f ∣[k] tRep_gen D σ`. -/
private lemma exists_tRep_gen_eq_slash (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    ∃ σ : decompQuot (GL_pair 2) (HeckeCoset.rep D),
      f ∣[k] g = f ∣[k] tRep_gen (GL_pair 2) D σ := by
  have hadj_mem := GL_adjugate_mem_D D g hg hadj_rep
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hadj_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, hadj_eq⟩ := hadj_mem
  exact ⟨⟦⟨h₁, hh₁⟩⟧, slash_eq_tRep_gen_of_adj_mem k f hf D g h₁ h₂ hh₁ hh₂ hadj_eq⟩

/-- adj(rep(D_p)) ∈ D_p: the adjugate of the representative lies in the double coset.
For D_p = ⟦diag(1,p)⟧, adj(rep) is in D_p because adj(diag(1,p)) = diag(p,1) = T_p_lower ∈ D_p
and rep is in the same double coset as diag(1,p). -/
private lemma adj_rep_mem_D_p (p : ℕ) (hp : Nat.Prime p) :
    GL_adjugate (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) ∈
      HeckeCoset.toSet (D_p p hp.pos) := by
  -- rep ∈ D_p, so rep = a * diag * c with a, c ∈ H
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  -- adj(rep) = adj(a * diag * c) = adj(c) * adj(diag) * adj(a)
  -- adj(diag(1,p)) = diag(p,1) which is T_p_lower
  -- T_p_lower ∈ D_p, so adj(diag) ∈ D_p
  have hTl := T_p_lower_mem_D_p p hp
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨b₁, hb₁, b₂, hb₂, hTl_eq⟩ := hTl
  -- adj(rep) = adj(c) * adj(diag) * adj(a) and adj(diag) = b₁ * rep * b₂ (mod double coset)
  -- Wait, we need adj(diag) in terms of rep, not directly.
  -- Actually: adj(diag(1,p)) = [[p,0],[0,1]] = T_p_lower
  -- And T_p_lower ∈ D_p = HeckeCoset.toSet (D_p p hp.pos)
  -- So adj(diag(1,p)) ∈ H * rep * H, i.e., adj(diag(1,p)) = b₁ * rep * b₂.
  -- Then adj(rep) = adj(a * diag * c) = adj(c) * adj(diag) * adj(a)
  --             = adj(c) * b₁ * rep * b₂ * adj(a)
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  -- Need to compute adj(diag(1,p))
  have hadj_diag : GL_adjugate (diagMat 2 ![1, p] : GL _ ℚ) =
      (T_p_lower p hp.pos : GL _ ℚ) := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    simp only [GL_adjugate_val, diagMat_val _ _ hpos]
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext x; fin_cases x <;> simp
    have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
    have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.of_apply, huniv, he0, he1,
        Finset.prod_singleton]
  -- Now use the factorisation: rep = a * diag * c, adj(diag) = T_p_lower = b₁ * rep * b₂
  refine ⟨GL_adjugate c * b₁,
    (GL_pair 2).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hb₁,
    b₂ * GL_adjugate a,
    (GL_pair 2).H.mul_mem hb₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  -- adj(rep) = adj(c) * adj(diag) * adj(a) = adj(c) * b₁ * rep * b₂ * adj(a)
  have h1 : GL_adjugate (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) =
      GL_adjugate c * GL_adjugate (diagMat 2 ![1, p]) * GL_adjugate a := by
    conv_lhs => rw [show (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) =
      a * diagMat 2 ![1, p] * c from hrep_eq]
    rw [GL_adjugate_mul, GL_adjugate_mul, mul_assoc]
  rw [h1, hadj_diag, hTl_eq]; group

/-! ### Coset sum equality: helper lemmas

The following lemmas establish that the `p + 1` explicit coset representatives
(`T_p_upper(b)` for `b < p` and `T_p_lower`) biject onto `decompQuot`
via the adjugate factorisation. -/

/-- Elements of `SLnZ_subgroup 2` have integer entries. -/
private lemma SLnZ_entry_is_int (g : GL (Fin 2) ℚ) (hg : g ∈ SLnZ_subgroup 2)
    (i j : Fin 2) : ∃ n : ℤ, g.val i j = (n : ℚ) := by
  obtain ⟨s, rfl⟩ := hg
  exact ⟨s.val i j, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- Auxiliary: the double coset membership proof for `adj(g)`, rewritten to
the `DoubleCoset.mem_doubleCoset` form. -/
private noncomputable def adj_mem_dc
    (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (GL_pair 2).H) (h₂ : GL _ ℚ) (_ : h₂ ∈ (GL_pair 2).H),
      GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂ := by
  have := GL_adjugate_mem_D D g hg hadj_rep
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  obtain ⟨a, ha, b, hb, heq⟩ := this; exact ⟨a, ha, b, hb, heq⟩

-- Note: The `factored_sigma` helper approach was abandoned due to kernel-level timeouts
-- when elaborating `tRep_gen D (factored_sigma ...)`. The proof of
-- `tRep_gen_D_p_matches_T_p_reps` instead keeps all `adj_mem_dc` factorisations local,
-- defines `φ : Fin(p+1) → decompQuot` via `Classical.choose`, and proves injectivity
-- by extracting `adj(g₁)⁻¹ * adj(g₂) ∈ H` from quotient equality via `conjSub` membership.

/-- The `decompQuot` for `D_p` has cardinality `p + 1`. -/
private lemma card_decompQuot_D_p (p : ℕ) (hp : Nat.Prime p) :
    Fintype.card (decompQuot (GL_pair 2) (HeckeCoset.rep (D_p p hp.pos))) = p + 1 := by
  have h1 : D_p p hp.pos = T_diag (![1, p]) := by
    change ⟦⟨diagMat 2 ![1, p], _⟩⟧ = ⟦diagMat_delta 2 ![1, p]⟧
    unfold diagMat_delta; simp [dif_pos hp.pos]
  have h2 : HeckeCoset_deg (GL_pair 2) (D_p p hp.pos) = ↑(p + 1) := by
    rw [h1]; convert deg_T_diag_ppow p hp 0 1 (by omega) using 2
    · congr 1; ext i; fin_cases i <;> simp
    · simp
  simp only [HeckeCoset_deg] at h2; exact_mod_cast h2

set_option maxHeartbeats 1600000 in
/-- `adj(T_p_upper(b₁))⁻¹ · adj(T_p_upper(b₂)) ∉ SL₂(ℤ)` for distinct `b₁, b₂ < p`.
The product has `(0,1)`-entry `(b₁ - b₂)/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_not_mem_H (p : ℕ) (hp : Nat.Prime p)
    (b₁ b₂ : ℕ) (hb₁ : b₁ < p) (hb₂ : b₂ < p) (hne : b₁ ≠ b₂) :
    (GL_adjugate (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b₁ : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 : ℚ), ((b₁ : ℤ) - (b₂ : ℤ) : ℤ) / (p : ℚ); 0, 1])
      (by simp [det_fin_two]) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, sub_div] <;>
      (try ring) <;> field_simp <;> ring
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 0 1
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_rat : ((b₁ : ℤ) - (b₂ : ℤ) : ℚ) = (n : ℚ) * (p : ℚ) := by
    have := hn; field_simp at this ⊢; exact_mod_cast this
  have h_int : (b₁ : ℤ) - (b₂ : ℤ) = n * (p : ℤ) := by exact_mod_cast h_rat
  -- |b₁ - b₂| < p but b₁ - b₂ = n * p, so n = 0 and b₁ = b₂
  have : (p : ℤ) ∣ ((b₁ : ℤ) - b₂) := ⟨n, by linarith⟩
  have hlt : |(b₁ : ℤ) - b₂| < p := by
    rw [abs_lt]; constructor <;> [push_cast; push_cast] <;> omega
  rw [h_int] at hlt; simp [abs_mul, Nat.abs_cast] at hlt
  have hn0 : n = 0 := by
    by_contra h; exact absurd hlt (not_lt.mpr (le_mul_of_one_le_left (by omega) (Int.one_le_abs h)))
  simp [hn0] at h_int; omega

set_option maxHeartbeats 1600000 in
/-- `adj(T_p_upper(b))⁻¹ · adj(T_p_lower) ∉ SL₂(ℤ)`.
The product has `(0,0)`-entry `1/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_lower_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 / (p : ℚ)), (b : ℚ); 0, (p : ℚ)])
      (by norm_num [det_fin_two]; exact hp.ne_zero) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, T_p_lower, GeneralLinearGroup.mkOfDetNeZero] <;>
      (try ring) <;> field_simp
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 0 0
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have h_np : (n : ℚ) * p = 1 := by rw [← hn]; field_simp
  have h_int : n * (p : ℤ) = 1 := by exact_mod_cast h_np
  have : (p : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h_le := Int.le_of_dvd one_pos this
  linarith [show (1 : ℤ) < ↑p from Int.ofNat_lt.mpr hp.one_lt]

set_option maxHeartbeats 1600000 in
/-- `adj(T_p_lower)⁻¹ · adj(T_p_upper(b)) ∉ SL₂(ℤ)`.
The product has `(1,1)`-entry `1/p ∉ ℤ`. -/
lemma adj_lower_inv_mul_upper_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_lower p hp.pos : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(p : ℚ), -(b : ℚ); 0, 1 / (p : ℚ)])
      (by norm_num [det_fin_two]; exact hp.ne_zero) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, T_p_lower, GeneralLinearGroup.mkOfDetNeZero] <;>
      (try ring) <;> field_simp
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 1 1
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have h_np : (n : ℚ) * p = 1 := by rw [← hn]; field_simp
  have h_int : n * (p : ℤ) = 1 := by exact_mod_cast h_np
  have : (p : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h_le := Int.le_of_dvd one_pos this
  linarith [show (1 : ℤ) < ↑p from Int.ofNat_lt.mpr hp.one_lt]

/-- If two `H`-elements `a₁, a₂` represent the same class in `decompQuot D` and provide
double-coset factorisations `adj(gᵢ) = aᵢ · rep · cᵢ`, then `adj(g₁)⁻¹ · adj(g₂) ∈ H`.
The quotient equality gives `rep⁻¹ · (a₁⁻¹ · a₂) · rep ∈ H`, which conjugates into the
goal `c₁⁻¹ · (rep⁻¹ · a₁⁻¹ · a₂ · rep) · c₂ ∈ H`. -/
private lemma adj_inv_mul_mem_H_of_decompQuot_eq (D : HeckeCoset (GL_pair 2))
    (a₁ : GL _ ℚ) (ha₁ : a₁ ∈ (GL_pair 2).H) (c₁ : GL _ ℚ) (hc₁ : c₁ ∈ (GL_pair 2).H)
    (a₂ : GL _ ℚ) (ha₂ : a₂ ∈ (GL_pair 2).H) (c₂ : GL _ ℚ) (hc₂ : c₂ ∈ (GL_pair 2).H)
    (g₁ g₂ : GL _ ℚ)
    (heq₁ : GL_adjugate g₁ = a₁ * (HeckeCoset.rep D : GL _ ℚ) * c₁)
    (heq₂ : GL_adjugate g₂ = a₂ * (HeckeCoset.rep D : GL _ ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (GL_pair 2).H)⟧ : decompQuot (GL_pair 2) (HeckeCoset.rep D)) =
      ⟦⟨a₂, ha₂⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (GL_pair 2).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv,
    Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  -- hrel: rep⁻¹ * (a₁⁻¹ * a₂) * rep ∈ H
  rw [show (a₁ * ↑(HeckeCoset.rep D) * c₁)⁻¹ * (a₂ * ↑(HeckeCoset.rep D) * c₂) =
      c₁⁻¹ * ((↑(HeckeCoset.rep D))⁻¹ * (a₁⁻¹ * a₂) * ↑(HeckeCoset.rep D)) * c₂ from by group]
  exact (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc₁) hrel) hc₂

/-- Reindex the explicit `T_p` coset sum `(∑_{j < p} F j) + G` as a single sum over
`Fin (p + 1)` with a `dite` selecting the upper terms `F` for `j < p` and the lower term
`G` for `j = p`. -/
private lemma sum_range_add_eq_sum_fin_succ_dite {M : Type*} [AddCommMonoid M]
    (p : ℕ) (F : ℕ → M) (G : M) :
    (∑ j ∈ Finset.range p, F j) + G =
    ∑ j : Fin (p + 1), if _h : (j : ℕ) < p then F (j : ℕ) else G := by
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_castSucc]; congr 1
  · congr 1; ext j; simp [j.isLt]
  · simp

/-- The `p + 1` adjugated `T_p` representatives lie in distinct left `H`-cosets:
for `j₁ ≠ j₂` the product `adj(gⱼ₁)⁻¹ · adj(gⱼ₂) ∉ H`, where `gⱼ` is `T_p_upper j`
for `j < p` and `T_p_lower` for `j = p`. Dispatches to the three matrix-entry lemmas. -/
private lemma adj_Tp_rep_inv_mul_not_mem_H (p : ℕ) (hp : Nat.Prime p)
    (j₁ j₂ : Fin (p + 1)) (hne : j₁ ≠ j₂) :
    (GL_adjugate (if (j₁ : ℕ) < p then T_p_upper p hp.pos (j₁ : ℕ)
        else T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (if (j₂ : ℕ) < p then T_p_upper p hp.pos (j₂ : ℕ)
        else T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  split_ifs
  · exact adj_upper_inv_mul_not_mem_H p hp (j₁ : ℕ) (j₂ : ℕ) ‹(j₁ : ℕ) < p› ‹(j₂ : ℕ) < p›
      (fun h => hne (Fin.ext h))
  · exact adj_upper_inv_mul_lower_not_mem_H p hp (j₁ : ℕ)
  · exact adj_lower_inv_mul_upper_not_mem_H p hp (j₂ : ℕ)
  · exact absurd (Fin.ext (show (j₁ : ℕ) = (j₂ : ℕ) by
      have := j₁.isLt; have := j₂.isLt; omega)) hne

/-- Abstract coset-sum equality. Given representatives `g j` of the double coset `D`
whose adjugates factor as `adj(g j) = h₁ · rep · h₂` (so each `g j` matches some
`tRep_gen` class), with the index set equinumerous to `decompQuot D` and the classes
pairwise distinct (`adj(g j₁)⁻¹ · adj(g j₂) ∉ H` for `j₁ ≠ j₂`), the abstract sum
`∑_σ f ∣[k] tRep_gen σ` equals the explicit sum `∑_j f ∣[k] g j`. -/
private lemma sum_tRep_gen_eq_sum_of_adj_factored {ι : Type*} [Fintype ι] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (D : HeckeCoset (GL_pair 2)) (g : ι → GL (Fin 2) ℚ)
    (hcard : Fintype.card ι = Fintype.card (decompQuot (GL_pair 2) (HeckeCoset.rep D)))
    (hfac : ∀ j, ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (GL_pair 2).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (GL_pair 2).H),
        GL_adjugate (g j) = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (hdist : ∀ j₁ j₂, j₁ ≠ j₂ →
        (GL_adjugate (g j₁))⁻¹ * GL_adjugate (g j₂) ∉ (GL_pair 2).H) :
    ∑ σ : decompQuot (GL_pair 2) (HeckeCoset.rep D), f ∣[k] tRep_gen (GL_pair 2) D σ =
    ∑ j, f ∣[k] g j := by
  classical
  let φ : ι → decompQuot (GL_pair 2) (HeckeCoset.rep D) := fun j =>
    ⟦⟨(hfac j).choose, (hfac j).choose_spec.choose⟩⟧
  have h_val : ∀ j, f ∣[k] g j = f ∣[k] tRep_gen (GL_pair 2) D (φ j) := fun j =>
    slash_eq_tRep_gen_of_adj_mem k f hf D _ _ _ (hfac j).choose_spec.choose
      (hfac j).choose_spec.choose_spec.choose_spec.choose
      (hfac j).choose_spec.choose_spec.choose_spec.choose_spec
  have h_inj : Function.Injective φ := by
    intro j₁ j₂ heq
    by_contra hne
    refine hdist j₁ j₂ hne (adj_inv_mul_mem_H_of_decompQuot_eq D
      (hfac j₁).choose (hfac j₁).choose_spec.choose
      (hfac j₁).choose_spec.choose_spec.choose
      (hfac j₁).choose_spec.choose_spec.choose_spec.choose
      (hfac j₂).choose (hfac j₂).choose_spec.choose
      (hfac j₂).choose_spec.choose_spec.choose
      (hfac j₂).choose_spec.choose_spec.choose_spec.choose
      (g j₁) (g j₂) (hfac j₁).choose_spec.choose_spec.choose_spec.choose_spec
      (hfac j₂).choose_spec.choose_spec.choose_spec.choose_spec heq)
  have h_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]; exact ⟨h_inj, hcard⟩
  exact (Fintype.sum_bijective φ h_bij _ _ h_val).symm

set_option maxHeartbeats 6400000 in
theorem tRep_gen_D_p_matches_T_p_reps (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∑ i : decompQuot (GL_pair 2) (HeckeCoset.rep (D_p p hp.pos)),
      f ∣[k] tRep_gen (GL_pair 2) (D_p p hp.pos) i =
    (∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set D := D_p p hp.pos
  have hadj_rep := adj_rep_mem_D_p p hp
  -- The `p + 1` explicit representatives, indexed by `Fin (p + 1)`: `T_p_upper b` for
  -- `b < p` and `T_p_lower` for the last index.
  set g : Fin (p + 1) → GL (Fin 2) ℚ := fun j =>
    if (j : ℕ) < p then T_p_upper p hp.pos (j : ℕ) else T_p_lower p hp.pos with hg
  -- Each `g j` lies in the double coset `D`, so `adj(g j)` factors through `rep`.
  have hmem : ∀ j, g j ∈ HeckeCoset.toSet D := by
    intro j; simp only [hg]; split_ifs with h
    · exact T_p_upper_mem_D_p p hp (j : ℕ) h
    · exact T_p_lower_mem_D_p p hp
  have hfac := fun j => adj_mem_dc D (g j) (hmem j) hadj_rep
  -- The representatives lie in pairwise distinct left `H`-cosets.
  have hdist : ∀ j₁ j₂ : Fin (p + 1), j₁ ≠ j₂ →
      (GL_adjugate (g j₁))⁻¹ * GL_adjugate (g j₂) ∉ (GL_pair 2).H := by
    intro j₁ j₂ hne; simp only [hg]; exact adj_Tp_rep_inv_mul_not_mem_H p hp j₁ j₂ hne
  -- Reduce the abstract sum to `∑_j f ∣[k] g j`, then reindex `g` to the explicit form.
  rw [sum_tRep_gen_eq_sum_of_adj_factored k f hf D g
      (by rw [Fintype.card_fin]; exact (card_decompQuot_D_p p hp).symm) hfac hdist,
    sum_range_add_eq_sum_fin_succ_dite p
      (fun n => f ∣[k] (T_p_upper p hp.pos n : GL (Fin 2) ℚ))
      (f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hg]; split_ifs <;> rfl

/-! ### Main theorem: diamond triviality and heckeT_p_fun = heckeSlash_gen -/

/-- For an SL₂(ℤ)-invariant modular form, the diamond operator acts trivially:
`⟨d⟩f = f` for any `d ∈ (ℤ/Nℤ)ˣ`, because every `Γ₀(N)` element lies in `SL₂(ℤ)`. -/
lemma diamondOp_trivial_of_SL_invariant {N : ℕ} [NeZero N] (k : ℤ) (u : (ZMod N)ˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    ⇑(diamondOp k u f) = ⇑f := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective u
  rw [diamondOp_eq_diamondOpAux k u g hg]
  change (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) = ⇑f
  exact hf_SL _ ⟨g, rfl⟩

/-- **Main theorem.** For an SL₂(ℤ)-invariant function `f : ℍ → ℂ`, the explicit
Hecke operator `T_p` (at any level N with `gcd(p,N) = 1`) reduces on SL₂(ℤ)-invariant
forms to the abstract Hecke operator `heckeSlash_gen (GL_pair 2) k (D_p p)`:

  `heckeT_p_fun k p f = heckeSlash_gen (GL_pair 2) k (D_p p) f`

This connects Diamond-Shurman's explicit coset representative formula (Prop 5.2.1) to
Shimura's abstract Hecke algebra action (Prop 3.30). -/
theorem heckeT_p_fun_eq_heckeSlash_gen {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p_fun k p hp hpN f =
    heckeSlash_gen (GL_pair 2) k (D_p p hp.pos) (⇑f) := by
  -- Unfold heckeSlash_gen to the sum over decompQuot
  rw [heckeSlash_gen]
  -- Use the core matching theorem
  rw [tRep_gen_D_p_matches_T_p_reps k p hp (⇑f) hf_SL]
  -- heckeT_p_fun = upper sum + (diamond f)|T_p_lower
  -- For SL₂(ℤ)-invariant f, diamond is trivial, so (diamond f)|T_p_lower = f|T_p_lower
  simp only [heckeT_p_fun, heckeT_p_ut]
  congr 1
  congr 1
  exact diamondOp_trivial_of_SL_invariant k _ f hf_SL

/-! ### Commutativity corollary -/

/-- The heckeSlash_gen operators commute for GL_pair 2 because the Hecke algebra
`𝕋 (GL_pair 2) ℤ` is commutative. -/
theorem heckeSlash_gen_GL_pair_comm (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f) :
    heckeSlash_gen (GL_pair 2) k D₁ (heckeSlash_gen (GL_pair 2) k D₂ f) =
    heckeSlash_gen (GL_pair 2) k D₂ (heckeSlash_gen (GL_pair 2) k D₁ f) :=
  heckeSlash_gen_comm k D₁ D₂ f hf (fun _ _ => mul_comm _ _)

/-- Convert SL₂(ℤ)-invariance (via `𝒮ℒ ⊂ GL₂(ℝ)`) to `(GL_pair 2).H`-invariance
(via `glMap`). -/
private lemma SL_invariant_to_H_invariant {k : ℤ} {f : ℍ → ℂ}
    (hf_SL : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f := by
  intro h hh; obtain ⟨s, hs⟩ := hh; rw [← hs]
  exact hf_SL (glMap (mapGL ℚ s)) ⟨s, (glMap_mapGL_eq s).symm⟩

/-- SL₂(ℤ)-invariance of `heckeSlash_gen (GL_pair 2) k D f` when `f` is SL₂(ℤ)-invariant.
Follows from `heckeSlash_gen_slash_invariant`. -/
private lemma heckeSlash_gen_SL_invariant {k : ℤ} (D : HeckeCoset (GL_pair 2)) {f : ℍ → ℂ}
    (hf_SL : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∀ γ ∈ 𝒮ℒ, (heckeSlash_gen (GL_pair 2) k D f) ∣[k] γ =
      heckeSlash_gen (GL_pair 2) k D f := by
  intro γ hγ; obtain ⟨s, hs⟩ := hγ
  -- Convert the GL₂(ℝ) element back to a GL₂(ℚ) element
  have hmem : mapGL ℚ s ∈ (GL_pair 2).H := ⟨s, rfl⟩
  -- The slash by γ = mapGL ℝ s equals slash by mapGL ℚ s (via glMap)
  rw [← hs]
  change (heckeSlash_gen (GL_pair 2) k D f) ∣[k] glMap (mapGL ℚ s) =
    heckeSlash_gen (GL_pair 2) k D f
  rw [show (heckeSlash_gen (GL_pair 2) k D f) ∣[k] glMap (mapGL ℚ s) =
    (heckeSlash_gen (GL_pair 2) k D f) ∣[k] (mapGL ℚ s : GL _ ℚ) from rfl]
  exact heckeSlash_gen_slash_invariant k D f (SL_invariant_to_H_invariant hf_SL) _ hmem

/-- **Commutativity of Hecke operators at level 1.**
For SL₂(ℤ)-invariant `f`, the Hecke operators `T_p` and `T_q` commute:
`T_p(T_q(f)) = T_q(T_p(f))`.

The proof reduces to `heckeSlash_gen_comm` via `heckeT_p_fun_eq_heckeSlash_gen`,
using commutativity of the Hecke algebra `𝕋 (GL_pair 2) ℤ`. -/
theorem heckeT_p_fun_comm_of_GL_pair {N : ℕ} [NeZero N] (k : ℤ)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p_fun k p hp hpN (⟨⟨heckeT_p_fun k q hq hqN f,
        (heckeT_p k q hq hqN f).slash_action_eq'⟩,
        (heckeT_p k q hq hqN f).holo',
        (heckeT_p k q hq hqN f).bdd_at_cusps'⟩ : ModularForm _ k) =
    heckeT_p_fun k q hq hqN (⟨⟨heckeT_p_fun k p hp hpN f,
        (heckeT_p k p hp hpN f).slash_action_eq'⟩,
        (heckeT_p k p hp hpN f).holo',
        (heckeT_p k p hp hpN f).bdd_at_cusps'⟩ : ModularForm _ k) := by
  -- SL₂(ℤ)-invariance transfers via heckeSlash_gen
  have hTqf_SL : ∀ γ ∈ 𝒮ℒ,
      heckeT_p_fun k q hq hqN f ∣[k] γ = heckeT_p_fun k q hq hqN f := by
    intro γ hγ
    rw [heckeT_p_fun_eq_heckeSlash_gen k q hq hqN f hf_SL]
    exact heckeSlash_gen_SL_invariant (D_p q hq.pos) hf_SL γ hγ
  have hTpf_SL : ∀ γ ∈ 𝒮ℒ,
      heckeT_p_fun k p hp hpN f ∣[k] γ = heckeT_p_fun k p hp hpN f := by
    intro γ hγ
    rw [heckeT_p_fun_eq_heckeSlash_gen k p hp hpN f hf_SL]
    exact heckeSlash_gen_SL_invariant (D_p p hp.pos) hf_SL γ hγ
  -- Bundle T_q(f) and T_p(f) as ModularForms for applying heckeT_p_fun_eq_heckeSlash_gen
  set Tqf : ModularForm _ k :=
    ⟨⟨heckeT_p_fun k q hq hqN f, (heckeT_p k q hq hqN f).slash_action_eq'⟩,
     (heckeT_p k q hq hqN f).holo', (heckeT_p k q hq hqN f).bdd_at_cusps'⟩
  set Tpf : ModularForm _ k :=
    ⟨⟨heckeT_p_fun k p hp hpN f, (heckeT_p k p hp hpN f).slash_action_eq'⟩,
     (heckeT_p k p hp hpN f).holo', (heckeT_p k p hp hpN f).bdd_at_cusps'⟩
  -- Rewrite heckeT_p_fun to heckeSlash_gen on the outer layer
  rw [heckeT_p_fun_eq_heckeSlash_gen k p hp hpN Tqf hTqf_SL,
      heckeT_p_fun_eq_heckeSlash_gen k q hq hqN Tpf hTpf_SL]
  -- Unfold the ModularForm coercions to heckeT_p_fun
  change heckeSlash_gen (GL_pair 2) k (D_p p hp.pos) (heckeT_p_fun k q hq hqN f) =
    heckeSlash_gen (GL_pair 2) k (D_p q hq.pos) (heckeT_p_fun k p hp hpN f)
  -- Rewrite the inner heckeT_p_fun to heckeSlash_gen
  conv_lhs => rw [heckeT_p_fun_eq_heckeSlash_gen k q hq hqN f hf_SL]
  conv_rhs => rw [heckeT_p_fun_eq_heckeSlash_gen k p hp hpN f hf_SL]
  exact heckeSlash_gen_GL_pair_comm k (D_p p hp.pos) (D_p q hq.pos) (⇑f)
    (SL_invariant_to_H_invariant hf_SL)

/-- Cleaner version using the `heckeT_p` linear map directly. -/
theorem heckeT_p_comm {N : ℕ} [NeZero N] (k : ℤ)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p k p hp hpN (heckeT_p k q hq hqN f) =
    heckeT_p k q hq hqN (heckeT_p k p hp hpN f) := by
  ext z
  show heckeT_p_fun k p hp hpN (heckeT_p k q hq hqN f) z =
    heckeT_p_fun k q hq hqN (heckeT_p k p hp hpN f) z
  exact congr_fun (heckeT_p_fun_comm_of_GL_pair k p q hp hq hpN hqN f hf_SL) z

end HeckeRing.GL2
