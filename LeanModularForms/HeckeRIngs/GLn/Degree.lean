/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CosetDecomposition
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree
import LeanModularForms.HeckeRIngs.GLn.CongruenceIndex

/-!
# Degree Formulas for GL_n Hecke Ring

Degree formulas for the diagonal Hecke operators `T(a₁,...,aₙ)`, including Gaussian binomial
coefficients for the prime-power case.

## Main definitions

* `gaussianBinom q n k` : the Gaussian binomial coefficient `[n choose k]_q`

## Main results

* `upperTriRep_card_le_T'_deg` : `∏_{i<j} (a_j / a_i) ≤ deg(T(a₁,...,aₙ))`

## Important note on degree formulas

The degree of `T(a₁,...,aₙ)` is **not** simply `∏_{i<j} (aⱼ/aᵢ)`. The upper-triangular
representatives with fixed diagonal `(a₁,...,aₙ)` account for `∏_{i<j}(aⱼ/aᵢ)` left cosets,
but the double coset also contains representatives with permuted diagonals (those whose
Hermite Normal Form has a different diagonal but the same Smith Normal Form).

**Counterexample:** For `n = 2`, `a = (1, p)` with `p` prime, the `UpperTriRep` count is `p`,
but the actual degree is `p + 1`. The additional representative is `[[p,0],[0,1]]`, which lies
in the double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` but has a different diagonal.

**Correct formula for n = 2:** `deg(T(a₁,a₂)) = ψ(a₂/a₁)` where `ψ` is the Dedekind psi
function `ψ(d) = d · ∏_{p | d} (1 + 1/p)`. For the prime-power case needed for Theorem 3.24:
`deg(T(pⁱ, pⁱ⁺ᵏ)) = pᵏ⁻¹(p + 1)` for `k ≥ 1`.

## References

* Shimura, Proposition 3.14, 3.18, Theorem 3.24
-/

open HeckeRing Finset CongruenceSubgroup Matrix.SpecialLinearGroup Matrix ModularGroup
open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-! ### Gaussian binomial coefficients -/

/-- Gaussian binomial coefficient `[n choose k]_q = ∏_{i=0}^{k-1} (qⁿ⁻ⁱ - 1) / (qᵏ⁻ⁱ - 1)`.
    Counts the number of `k`-dimensional subspaces of `𝔽_q^n`. -/
def gaussianBinom (q : ℕ) (m k : ℕ) : ℕ :=
  if k ≤ m then
    (Finset.range k).prod fun i => (q ^ (m - i) - 1) / (q ^ (k - i) - 1)
  else 0

lemma gaussianBinom_zero_right (q m : ℕ) : gaussianBinom q m 0 = 1 := by
  simp [gaussianBinom]

lemma gaussianBinom_gt (q m k : ℕ) (h : m < k) : gaussianBinom q m k = 0 := by
  simp [gaussianBinom, Nat.not_le.mpr h]

/-- Conjugation by an element of H preserves H. -/
private lemma conjAct_smul_eq_of_mem {G : Type*} [Group G] (H : Subgroup G)
    {h : G} (hh : h ∈ H) :
    ConjAct.toConjAct h • H = H := by
  ext x; constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h_eq : ConjAct.toConjAct h • ((ConjAct.toConjAct h)⁻¹ • x) = x :=
      smul_inv_smul _ x
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h_eq
    rw [← h_eq]; exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (ConjAct.toConjAct h)⁻¹ • x = h⁻¹ * x * h := by
      show ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹ * x *
        (ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹)⁻¹ = _
      simp [ConjAct.ofConjAct_toConjAct, mul_assoc]
    rw [this]; exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

/-! ### Degree lower bound from upper-triangular representatives -/

variable (n : ℕ) [NeZero n]

/-! #### Helpers for the degree lower bound -/

/-- The unipotent SL element associated to an upper-triangular representative. -/
private def unipSL (a : Fin n → ℕ+) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    SL(n, ℤ) :=
  ⟨unipMat n a hdiv B, unipMat_det n a hdiv B⟩

/-- `upperTriGL B = diagMat n a * SLnZ_to_GLnQ n (unipSL B)`. -/
private lemma upperTriGL_eq_diagMat_mul (a : Fin n → ℕ+) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) :
    upperTriGL n a hdiv B = diagMat n a * SLnZ_to_GLnQ n (unipSL n a hdiv B) := by
  apply Units.ext
  simp only [upperTriGL_val, Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_mul, one_mul, zero_mul]
    simp only [unipSL, unipMat, upperTriMat]
    split_ifs <;> push_cast <;> ring
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Inverse-transpose automorphism of SL_n(ℤ): σ ↦ (σᵀ)⁻¹.
    This is a MulEquiv because transpose and inverse are each anti-homomorphisms. -/
private def invTransposeEquiv : SL(n, ℤ) ≃* SL(n, ℤ) where
  toFun σ := σ.transpose⁻¹
  invFun σ := σ⁻¹.transpose
  left_inv σ := by
    show (σ.transpose⁻¹)⁻¹.transpose = σ
    simp only [inv_inv]; ext i j; simp [coe_transpose]
  right_inv σ := by
    show (σ⁻¹.transpose).transpose⁻¹ = σ
    have : (σ⁻¹.transpose).transpose = σ⁻¹ := by
      ext i j; simp [coe_transpose]
    rw [this, inv_inv]
  map_mul' σ τ := by
    show (σ * τ).transpose⁻¹ = σ.transpose⁻¹ * τ.transpose⁻¹
    have h : (σ * τ).transpose = τ.transpose * σ.transpose := by
      apply Subtype.ext
      simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_transpose,
        Matrix.transpose_mul]
    rw [h, _root_.mul_inv_rev]

/-- For SL elements, inverse commutes with transpose: `σᵀ⁻¹ = σ⁻¹ᵀ`. -/
private lemma SL_transpose_inv_eq (σ : SL(n, ℤ)) :
    σ.transpose⁻¹ = σ⁻¹.transpose := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_transpose,
    Matrix.adjugate_transpose]

/-- The inverse-transpose map is an involution. -/
private lemma invTransposeEquiv_invol (σ : SL(n, ℤ)) :
    invTransposeEquiv n (invTransposeEquiv n σ) = σ := by
  have : invTransposeEquiv n σ = (invTransposeEquiv n).symm σ := by
    show σ.transpose⁻¹ = σ⁻¹.transpose
    exact SL_transpose_inv_eq n σ
  rw [this]; exact (invTransposeEquiv n).apply_symm_apply σ

/-- For a diagonal matrix α and injective embedding f : SL_n(ℤ) →* GL_n(ℚ) with range H,
    the relIndex `K.relIndex H` equals `(K.comap f).index`. -/
private lemma relIndex_eq_comap_index (K : Subgroup (GL (Fin n) ℚ)) :
    K.relIndex (SLnZ_subgroup n) = (K.comap (SLnZ_to_GLnQ n)).index := by
  set f := SLnZ_to_GLnQ n
  set H := SLnZ_subgroup n
  have h_inj : Function.Injective f := by
    intro x y hxy; ext i j
    have h := congr_arg (fun g => (Units.val g) i j) hxy
    simp only [f, SLnZ_to_GLnQ_val, Matrix.map_apply] at h; exact_mod_cast h
  have h_H_eq : H = Subgroup.map f ⊤ := by
    simp only [H, SLnZ_subgroup]; exact MonoidHom.range_eq_map f
  have h_inf : K ⊓ H = Subgroup.map f (K.comap f) := by
    rw [h_H_eq, ← MonoidHom.range_eq_map f, inf_comm, Subgroup.map_comap_eq]
  calc K.relIndex H
      = (K ⊓ H).relIndex H := (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (K.comap f)).relIndex (Subgroup.map f ⊤) := by rw [h_inf, h_H_eq]
    _ = (K.comap f).relIndex ⊤ := Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (K.comap f).index := (K.comap f).relIndex_top_right

/-- Matrix-level transpose: from `f(σ) * α = α * f(ρ)`, derive `α * f(σᵀ) = f(ρᵀ) * α`
    (where α = diagMat is symmetric under transpose). -/
private lemma transpose_mul_diagMat (a : Fin n → ℕ+) (σ ρ : SL(n, ℤ))
    (h : SLnZ_to_GLnQ n σ * diagMat n a = diagMat n a * SLnZ_to_GLnQ n ρ) :
    diagMat n a * SLnZ_to_GLnQ n σ.transpose =
    SLnZ_to_GLnQ n ρ.transpose * diagMat n a := by
  apply Units.ext
  simp only [Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val,
    SpecialLinearGroup.coe_transpose, Matrix.transpose_map]
  have hM := congr_arg Units.val h
  simp only [Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val] at hM
  have h1 := congr_arg Matrix.transpose hM
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose] at h1
  exact h1

/-- S2: The left and right coset counts are equal for diagonal matrices (d = e).
    Uses the inverse-transpose automorphism: transpose sends `H ∩ αHα⁻¹` to `H ∩ α⁻¹Hα`
    for diagonal α. -/
private lemma relIndex_conj_inv_eq_conj_diag (a : Fin n → ℕ+) :
    (ConjAct.toConjAct (diagMat n a)⁻¹ • SLnZ_subgroup n).relIndex (SLnZ_subgroup n) =
    (ConjAct.toConjAct (diagMat n a) • SLnZ_subgroup n).relIndex (SLnZ_subgroup n) := by
  rw [relIndex_eq_comap_index, relIndex_eq_comap_index]
  set H := SLnZ_subgroup n
  set α := diagMat n a
  set f := SLnZ_to_GLnQ n
  set GammaMinus := (ConjAct.toConjAct α⁻¹ • H).comap f
  set GammaPlus := (ConjAct.toConjAct α • H).comap f
  set φ := invTransposeEquiv n
  suffices h_map : GammaPlus = GammaMinus.map φ.toMonoidHom by
    rw [h_map]; simp [Subgroup.index_map_equiv]
  -- Key helper: transpose sends Γ₊ into Γ₋
  have h_transpose_fwd : ∀ σ : SL(n, ℤ),
      f σ ∈ ConjAct.toConjAct α • H →
      f σ.transpose ∈ ConjAct.toConjAct α⁻¹ • H := by
    intro σ hσ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct] at hσ
    -- hσ : α⁻¹ * f σ * (α⁻¹)⁻¹ ∈ H, i.e., α⁻¹ * f σ * α ∈ H
    simp only [inv_inv] at hσ
    obtain ⟨ρ, hρ⟩ := (MonoidHom.mem_range.mp (show _ ∈ f.range from hσ))
    -- hρ : f ρ = α⁻¹ * f σ * α, so f σ * α = α * f ρ
    have h_eq : f σ * α = α * f ρ := by rw [hρ]; group
    have h_trans : α * f σ.transpose = f ρ.transpose * α :=
      transpose_mul_diagMat n a σ ρ h_eq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    have : α * f σ.transpose * α⁻¹ = f ρ.transpose := by
      have h := congr_arg (· * α⁻¹) h_trans
      simp only [mul_assoc, mul_inv_cancel, mul_one] at h
      rwa [← mul_assoc] at h
    rw [this]; exact ⟨ρ.transpose, rfl⟩
  -- Symmetric helper: transpose sends Γ₋ into Γ₊
  have h_transpose_bwd : ∀ τ : SL(n, ℤ),
      f τ ∈ ConjAct.toConjAct α⁻¹ • H →
      f τ.transpose ∈ ConjAct.toConjAct α • H := by
    intro τ hτ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hτ
    -- hτ : α * f τ * α⁻¹ ∈ H
    obtain ⟨ρ, hρ⟩ := (MonoidHom.mem_range.mp (show _ ∈ f.range from hτ))
    -- hρ : f ρ = α * f τ * α⁻¹, so f ρ * α = α * f τ
    have h_eq : f ρ * α = α * f τ := by rw [hρ]; group
    have h_trans : α * f ρ.transpose = f τ.transpose * α :=
      transpose_mul_diagMat n a ρ τ h_eq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
    simp only [inv_inv]
    have : α⁻¹ * f τ.transpose * α = f ρ.transpose := by
      have := congr_arg (α⁻¹ * ·) h_trans.symm
      simp only [← mul_assoc, inv_mul_cancel, one_mul] at this; exact this
    rw [this]; exact ⟨ρ.transpose, rfl⟩
  -- Prove set equality: GammaPlus = GammaMinus.map φ
  ext σ
  simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  constructor
  · -- σ ∈ GammaPlus → ∃ τ ∈ GammaMinus, φ(τ) = σ
    intro hσ
    refine ⟨φ σ, ?_, invTransposeEquiv_invol n σ⟩
    -- Need: φ(σ) ∈ GammaMinus, i.e., f(σᵀ⁻¹) ∈ α⁻¹ • H
    show f (φ σ) ∈ ConjAct.toConjAct α⁻¹ • H
    -- f(σᵀ) ∈ α⁻¹ • H by h_transpose_fwd
    have h_mem := h_transpose_fwd σ hσ
    -- f(σᵀ⁻¹) = f(σᵀ)⁻¹ ∈ α⁻¹ • H (subgroup closed under inv)
    have : f (φ σ) = (f σ.transpose)⁻¹ := by
      show f (σ.transpose⁻¹) = _; exact map_inv f _
    rw [this]
    exact (ConjAct.toConjAct α⁻¹ • H).inv_mem h_mem
  · -- ∃ τ ∈ GammaMinus, φ(τ) = σ → σ ∈ GammaPlus
    rintro ⟨τ, hτ, rfl⟩
    show f (φ τ) ∈ ConjAct.toConjAct α • H
    have h_mem := h_transpose_bwd τ hτ
    have : f (φ τ) = (f τ.transpose)⁻¹ := by
      show f (τ.transpose⁻¹) = _; exact map_inv f _
    rw [this]
    exact (ConjAct.toConjAct α • H).inv_mem h_mem

/-- The number of upper-triangular representatives is a lower bound on the degree.
    This is a strict inequality in general: for `n=2`, `a=(1,p)`, the LHS is `p`
    but the degree is `p + 1`. -/
theorem upperTriRep_card_le_T'_deg (a : Fin n → ℕ+) (hdiv : DivChain n a) :
    (Fintype.card (UpperTriRep n a hdiv) : ℤ) ≤
    T'_deg (GL_pair n) (T_diag n a hdiv) := by
  set H := (GL_pair n).H
  set D := T_diag n a hdiv
  set δ := (D.eql.choose : GL (Fin n) ℚ) with hδ_def
  set α := (diagMat n a : GL (Fin n) ℚ) with hα_def
  set f := SLnZ_to_GLnQ n
  have h_α_comm : α ∈ Subgroup.Commensurable.commensurator H :=
    (GL_pair n).h₁ (diagMat_mem_posDetInt n a)
  have h_α_inv_comm : α⁻¹ ∈ Subgroup.Commensurable.commensurator H :=
    (Subgroup.Commensurable.commensurator H).inv_mem h_α_comm
  have h_rel_ne : (ConjAct.toConjAct α⁻¹ • H).relIndex H ≠ 0 :=
    ((Subgroup.Commensurable.commensurator_mem_iff H α⁻¹).mp h_α_inv_comm).1
  haveI : Fintype (H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H) :=
    Subgroup.fintypeOfIndexNeZero h_rel_ne
  -- Step 1: Injection — card(UpperTriRep) ≤ (α⁻¹ • H).relIndex H
  have h_card_le : Fintype.card (UpperTriRep n a hdiv) ≤
      (ConjAct.toConjAct α⁻¹ • H).relIndex H := by
    have h_unip_mem : ∀ B, f (unipSL n a hdiv B) ∈ H := fun B => ⟨unipSL n a hdiv B, rfl⟩
    set injMap : UpperTriRep n a hdiv → H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H :=
      fun B => ⟦⟨(f (unipSL n a hdiv B))⁻¹, H.inv_mem (h_unip_mem B)⟩⟧
    have h_inj : Function.Injective injMap := by
      intro B₁ B₂ heq
      by_contra hne
      have hq := QuotientGroup.eq.mp heq
      rw [Subgroup.mem_subgroupOf] at hq
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at hq
      -- hq : f(B₁) * f(B₂)⁻¹ ∈ α⁻¹ • H
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hq
      -- hq : α * (f(B₁) * f(B₂)⁻¹) * α⁻¹ ∈ H
      -- Since upperTriGL B = α * f(unipSL B):
      have h1 : upperTriGL n a hdiv B₁ = α * f (unipSL n a hdiv B₁) :=
        upperTriGL_eq_diagMat_mul n a hdiv B₁
      have h2 : upperTriGL n a hdiv B₂ = α * f (unipSL n a hdiv B₂) :=
        upperTriGL_eq_diagMat_mul n a hdiv B₂
      have hmem : upperTriGL n a hdiv B₁ * (upperTriGL n a hdiv B₂)⁻¹ ∈ H := by
        suffices upperTriGL n a hdiv B₁ * (upperTriGL n a hdiv B₂)⁻¹ =
            α * (f (unipSL n a hdiv B₁) * (f (unipSL n a hdiv B₂))⁻¹) * α⁻¹ by
          rw [this]; exact hq
        rw [h1, h2]; group
      obtain ⟨γ, hγ⟩ := (MonoidHom.mem_range.mp (show _ ∈ f.range from hmem))
      have h_eq : upperTriGL n a hdiv B₁ = f γ * upperTriGL n a hdiv B₂ := by
        have hγ' : f γ = upperTriGL n a hdiv B₁ * (upperTriGL n a hdiv B₂)⁻¹ := hγ
        rw [hγ', mul_assoc, inv_mul_cancel, mul_one]
      exact upperTriMat_distinct_cosets n a hdiv B₁ B₂ hne (f γ) ⟨γ, rfl⟩ h_eq
    calc Fintype.card (UpperTriRep n a hdiv)
        ≤ Fintype.card (H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H) :=
          Fintype.card_le_of_injective injMap h_inj
      _ = (ConjAct.toConjAct α⁻¹ • H).relIndex H := by
          simp only [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]
  -- Step 2 (S2): (α⁻¹ • H).relIndex H = (α • H).relIndex H
  have h_S2 := relIndex_conj_inv_eq_conj_diag n a
  -- Step 3 (S1): (α • H).relIndex H = (δ • H).relIndex H
  have h_in_set : δ ∈ D.set := by
    rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [show D.set = DoubleCoset.doubleCoset α ↑H ↑H from rfl,
    DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_eq_of_mem H hσ₁
  have h_smul_σ₂ : ConjAct.toConjAct σ₂ • H = H := conjAct_smul_eq_of_mem H hσ₂
  have h_δ_smul : ConjAct.toConjAct δ • H = ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, MulAction.mul_smul, MulAction.mul_smul, h_smul_σ₂]
  have h_S1 : (ConjAct.toConjAct α • H).relIndex H =
      (ConjAct.toConjAct δ • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at this; exact this.symm
  -- Step 4: T'_deg = (δ • H).relIndex H
  have h_def : T'_deg (GL_pair n) D =
      ↑((ConjAct.toConjAct δ • H).relIndex H) := by
    simp only [T'_deg]; rw [← Nat.card_eq_fintype_card]; rfl
  -- Combine
  calc (Fintype.card (UpperTriRep n a hdiv) : ℤ)
      ≤ ↑((ConjAct.toConjAct α⁻¹ • H).relIndex H) := by exact_mod_cast h_card_le
    _ = ↑((ConjAct.toConjAct α • H).relIndex H) := by exact_mod_cast h_S2
    _ = ↑((ConjAct.toConjAct δ • H).relIndex H) := by exact_mod_cast h_S1
    _ = T'_deg (GL_pair n) D := h_def.symm

/-! ### Degree formula for n = 2 (prime-power case)

For `n = 2`, `a = (pⁱ, pⁱ⁺ᵏ)` with `k ≥ 1`:

  `deg(T(pⁱ, pⁱ⁺ᵏ)) = [SL₂(ℤ) : Γ₀(pᵏ)] = pᵏ⁻¹(p + 1)`

where `Γ₀(d) = {σ ∈ SL₂(ℤ) : d | σ₂₁}` is the standard congruence subgroup.

The proof uses the fact that `SL₂(ℤ)/Γ₀(d)` bijects to `ℙ¹(ℤ/dℤ)` via
`σ ↦ [σ₁₁ : σ₂₁]`, and `|ℙ¹(ℤ/pᵏℤ)| = pᵏ + pᵏ⁻¹ = pᵏ⁻¹(p + 1)`.
-/

/-! ### Helpers for the prime-power degree formula -/

/-- Key identity: a₁ = a₀ * p^k in ℚ (from the ratio and divisibility hypotheses). -/
private lemma a1_eq_a0_mul_pk {p : ℕ} {a : Fin 2 → ℕ+} {k : ℕ}
    (h_ratio : (a 1 : ℕ) / (a 0 : ℕ) = p ^ k) (h_dvd_a : (a 0 : ℕ) ∣ (a 1 : ℕ)) :
    (a 1 : ℚ) = (a 0 : ℚ) * (↑(p ^ k) : ℚ) := by
  have h1 := Nat.div_mul_cancel h_dvd_a; rw [h_ratio] at h1
  have : (a 1 : ℕ) = p ^ k * (a 0 : ℕ) := h1.symm
  push_cast [this]; ring

/-- For σ ∈ Gamma0(p^k) (i.e., p^k | σ₁₀), the conjugate α⁻¹σα lies in SL₂(ℤ). -/
private lemma conj_diagMat_mem_of_Gamma0 (a : Fin 2 → ℕ+) (k : ℕ)
    (h_ratio : (a 1 : ℕ) / (a 0 : ℕ) = p ^ k) (h_dvd_a : (a 0 : ℕ) ∣ (a 1 : ℕ))
    (σ : SL(2, ℤ)) (hσ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0) :
    (diagMat 2 a)⁻¹ * SLnZ_to_GLnQ 2 σ * diagMat 2 a ∈ SLnZ_subgroup 2 := by
  obtain ⟨c, hc⟩ := hσ
  -- Build the integer matrix for τ
  let τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![σ.1 0 0, ↑(p ^ k) * σ.1 0 1; c, σ.1 1 1]
  have h_det : τ_mat.det = 1 := by
    simp only [τ_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hσ_det := σ.prop; simp only [Matrix.det_fin_two] at hσ_det
    rw [hc] at hσ_det; linarith
  let τ : SL(2, ℤ) := ⟨τ_mat, h_det⟩
  rw [SLnZ_subgroup, MonoidHom.mem_range]
  refine ⟨τ, ?_⟩
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have hcQ : (σ.1 1 0 : ℚ) = (↑(p ^ k) : ℚ) * (c : ℚ) := by exact_mod_cast hc
  push_cast at ha1 hcQ
  -- Prove α * τ = σ * α (avoids matrix inverse entirely)
  suffices h : diagMat 2 a * SLnZ_to_GLnQ 2 τ = SLnZ_to_GLnQ 2 σ * diagMat 2 a by
    have h' := congr_arg ((diagMat 2 a)⁻¹ * ·) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h'; exact h'
  apply Units.ext; simp only [Units.val_mul, SLnZ_to_GLnQ_val]
  ext i j
  simp only [diagMat_val, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [τ, τ_mat, Matrix.of_apply, Matrix.cons_val', Fin.isValue] <;>
    push_cast <;> (try rw [hcQ]) <;> (try rw [ha1]) <;> ring

/-- If the conjugate α⁻¹σα lies in SL₂(ℤ), then p^k | σ₁₀. -/
private lemma Gamma0_of_conj_diagMat_mem (a : Fin 2 → ℕ+) (k : ℕ)
    (h_ratio : (a 1 : ℕ) / (a 0 : ℕ) = p ^ k) (h_dvd_a : (a 0 : ℕ) ∣ (a 1 : ℕ))
    (σ : SL(2, ℤ))
    (hmem : (diagMat 2 a)⁻¹ * SLnZ_to_GLnQ 2 σ * diagMat 2 a ∈ SLnZ_subgroup 2) :
    (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
  rw [SLnZ_subgroup, MonoidHom.mem_range] at hmem
  obtain ⟨τ, hτ⟩ := hmem
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have ha0_ne : (a 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (PNat.ne_zero _)
  -- From hτ: τ_GL = α⁻¹ * σ_GL * α, so α * τ_GL = σ_GL * α
  have h_mul : diagMat 2 a * SLnZ_to_GLnQ 2 τ = SLnZ_to_GLnQ 2 σ * diagMat 2 a := by
    have := congr_arg (diagMat 2 a * ·) hτ
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this; exact this
  -- Extract (1,0) entry: (a 1) * τ₁₀ = σ₁₀ * (a 0)
  have h_entry : (a 1 : ℚ) * (τ.1 1 0 : ℚ) = (σ.1 1 0 : ℚ) * (a 0 : ℚ) := by
    have h10 : ∀ i j, (↑(diagMat 2 a * SLnZ_to_GLnQ 2 τ) :
        Matrix (Fin 2) (Fin 2) ℚ) i j =
      (↑(SLnZ_to_GLnQ 2 σ * diagMat 2 a) : Matrix (Fin 2) (Fin 2) ℚ) i j := by
      intro i j; rw [Units.ext_iff.mp h_mul]
    have := h10 1 0
    simp only [Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply] at this
    exact this
  -- So σ₁₀ = (a₁/a₀) * τ₁₀ = p^k * τ₁₀
  have h_σ₁₀ : (σ.1 1 0 : ℚ) = ↑(p ^ k) * (τ.1 1 0 : ℚ) := by
    rw [ha1] at h_entry; field_simp at h_entry ⊢; linarith
  exact ⟨τ.1 1 0, by exact_mod_cast h_σ₁₀⟩

omit [NeZero n] in
/-- The relative index of the diagonal conjugate subgroup equals the Gamma0 index. -/
private lemma conjDiag_relIndex_eq_Gamma0_index (p : ℕ)
    (a : Fin 2 → ℕ+) (k : ℕ)
    (h_ratio : (a 1 : ℕ) / (a 0 : ℕ) = p ^ k) (h_dvd_a : (a 0 : ℕ) ∣ (a 1 : ℕ)) :
    (ConjAct.toConjAct (diagMat 2 a) • SLnZ_subgroup 2).relIndex (SLnZ_subgroup 2) =
    (Gamma0 (p ^ k)).index := by
  set H := SLnZ_subgroup 2
  set α := diagMat 2 a
  set f := SLnZ_to_GLnQ 2
  -- f is injective
  have h_inj : Function.Injective f := by
    intro σ₁ σ₂ h
    have := Units.ext_iff.mp h
    simp only [f, SLnZ_to_GLnQ] at this
    ext i j; exact Int.cast_injective (congr_fun₂ this i j)
  -- H = ⊤.map f
  have h_H_eq : H = Subgroup.map f ⊤ := by
    simp only [H, f, SLnZ_subgroup, MonoidHom.range_eq_map]
  -- Membership criterion: σ ∈ Gamma0(p^k) ↔ α⁻¹σα ∈ H
  have h_gamma0_iff : ∀ σ : SL(2, ℤ),
      σ ∈ Gamma0 (p ^ k) ↔ α⁻¹ * f σ * α ∈ H := by
    intro σ
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨conj_diagMat_mem_of_Gamma0 a k h_ratio h_dvd_a σ,
           Gamma0_of_conj_diagMat_mem a k h_ratio h_dvd_a σ⟩
  -- (αHα⁻¹ ⊓ H) = Gamma0.map f
  have h_inf_eq : (ConjAct.toConjAct α • H) ⊓ H = Subgroup.map f (Gamma0 (p ^ k)) := by
    ext g; simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h_smul, h_mem⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
      obtain ⟨σ, rfl⟩ := h_mem
      exact ⟨σ, (h_gamma0_iff σ).mpr h_smul, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, ⟨σ, rfl⟩⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      exact (h_gamma0_iff σ).mp hσ
  -- Chain: relIndex = inf_relIndex = map_relIndex = index
  calc (ConjAct.toConjAct α • H).relIndex H
      = ((ConjAct.toConjAct α • H) ⊓ H).relIndex H :=
          (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (Gamma0 (p ^ k))).relIndex (Subgroup.map f ⊤) := by
          rw [h_inf_eq, h_H_eq]
    _ = (Gamma0 (p ^ k)).relIndex ⊤ :=
          Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (Gamma0 (p ^ k)).index := (Gamma0 (p ^ k)).relIndex_top_right

/-- For n = 2 and prime `p`: `deg(T(pⁱ, pⁱ⁺ᵏ)) = pᵏ⁻¹(p + 1)` for `k ≥ 1`.
    This is Shimura, Theorem 3.24 part (6). -/
theorem T'_deg_T_diag_two_prime (p : ℕ) (hp : Nat.Prime p)
    (a : Fin 2 → ℕ+) (hdiv : DivChain 2 a) (k : ℕ) (hk : 0 < k)
    (h_ratio : (a 1 : ℕ) / (a 0 : ℕ) = p ^ k) :
    T'_deg (GL_pair 2) (T_diag 2 a hdiv) =
    ↑(p ^ (k - 1) * (p + 1)) := by
  set H := (GL_pair 2).H
  set D := T_diag 2 a hdiv
  set δ := (D.eql.choose : GL (Fin 2) ℚ) with hδ_def
  set α := (diagMat 2 a : GL (Fin 2) ℚ) with hα_def
  -- Step 1: Extract σ₁, σ₂ ∈ H with δ = σ₁ * α * σ₂
  have h_in_set : δ ∈ D.set := by
    rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [show D.set = DoubleCoset.doubleCoset α ↑H ↑H from rfl,
    DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  -- Step 2 (S1): T'_deg = relIndex with α
  have h_dvd_a : (a 0 : ℕ) ∣ (a 1 : ℕ) := divChain_dvd (n := 2) hdiv (Fin.zero_le 1)
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_eq_of_mem H hσ₁
  have h_smul_σ₂ : ConjAct.toConjAct σ₂ • H = H := conjAct_smul_eq_of_mem H hσ₂
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, MulAction.mul_smul, MulAction.mul_smul, h_smul_σ₂]
  have h_relIndex : (ConjAct.toConjAct δ • H).relIndex H =
      (ConjAct.toConjAct α • H).relIndex H := by
    rw [h_δ_smul]
    have h := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct σ₁)
      (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at h; exact h
  -- Step 3: Chain everything together
  simp only [T'_deg]
  rw [show (Fintype.card (decompQuot (GL_pair 2) D) : ℤ) =
    ↑(Nat.card (decompQuot (GL_pair 2) D)) from by rw [Nat.card_eq_fintype_card]]
  show ↑((ConjAct.toConjAct δ • H).relIndex H) = (↑(p ^ (k - 1) * (p + 1)) : ℤ)
  rw [h_relIndex, show H = SLnZ_subgroup 2 from rfl,
    conjDiag_relIndex_eq_Gamma0_index p a k h_ratio h_dvd_a,
    Gamma0_prime_power_index p hp k hk]

/-- A scalar diagonal matrix commutes with every element of `GL_n(ℚ)`. -/
private lemma diagMat_comm_of_const (a : Fin n → ℕ+) (h_const : ∀ i, a i = a 0)
    (g : GL (Fin n) ℚ) :
    diagMat n a * g = g * diagMat n a := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_val]
  have h_diag : Matrix.diagonal (fun i => (a i : ℚ)) =
      (a 0 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp [h_const]
    · simp
  rw [h_diag, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- For n = 2, scalar case: `deg(T(c, c)) = 1`. -/
theorem T'_deg_T_diag_two_scalar (a : Fin 2 → ℕ+) (hdiv : DivChain 2 a)
    (h_eq : a 0 = a 1) :
    T'_deg (GL_pair 2) (T_diag 2 a hdiv) = 1 := by
  have h_const : ∀ i : Fin 2, a i = a 0 := by intro i; fin_cases i <;> simp [h_eq]
  set D := T_diag 2 a hdiv
  set δ := (D.eql.choose : GL (Fin 2) ℚ) with hδ_def
  -- Step 1: δ ∈ DC(diagMat, H, H) — extract σ₁, σ₂ with δ = σ₁ * diagMat * σ₂
  have h_in_set : δ ∈ D.set := by
    rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [show D.set = DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ)
      ↑(GL_pair 2).H ↑(GL_pair 2).H from rfl,
    DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  -- Step 2: Conjugation by δ preserves H (diagMat is scalar, hence central)
  have h_comm := diagMat_comm_of_const 2 a h_const
  have h_conj_triv : ∀ y : GL (Fin 2) ℚ, (diagMat 2 a)⁻¹ * y * diagMat 2 a = y := by
    intro y
    calc (diagMat 2 a)⁻¹ * y * diagMat 2 a
        = (diagMat 2 a)⁻¹ * (y * diagMat 2 a) := by group
      _ = (diagMat 2 a)⁻¹ * (diagMat 2 a * y) := by rw [← h_comm y]
      _ = y := by group
  have hconj : (ConjAct.toConjAct δ • (GL_pair 2).H).subgroupOf (GL_pair 2).H = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    suffices h_eq : δ⁻¹ * x * δ = (σ₁ * σ₂)⁻¹ * x * (σ₁ * σ₂) by
      rw [h_eq]
      exact (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem
        ((GL_pair 2).H.inv_mem ((GL_pair 2).H.mul_mem hσ₁ hσ₂)) hx)
        ((GL_pair 2).H.mul_mem hσ₁ hσ₂)
    calc δ⁻¹ * x * δ
        = (σ₁ * diagMat 2 a * σ₂)⁻¹ * x * (σ₁ * diagMat 2 a * σ₂) := by rw [hδ_eq]
      _ = σ₂⁻¹ * ((diagMat 2 a)⁻¹ * (σ₁⁻¹ * x * σ₁) * diagMat 2 a) * σ₂ := by group
      _ = σ₂⁻¹ * (σ₁⁻¹ * x * σ₁) * σ₂ := by rw [h_conj_triv]
      _ = (σ₁ * σ₂)⁻¹ * x * (σ₁ * σ₂) := by group
  -- Step 3: Conclude T'_deg = 1
  simp only [T'_deg]
  haveI : Subsingleton (decompQuot (GL_pair 2) D) := by
    show Subsingleton ((GL_pair 2).H ⧸
      (ConjAct.toConjAct δ • (GL_pair 2).H).subgroupOf (GL_pair 2).H)
    rw [hconj]; exact QuotientGroup.subsingleton_quotient_top
  haveI := uniqueOfSubsingleton (⟦1⟧ : decompQuot (GL_pair 2) D)
  exact_mod_cast Fintype.card_unique

end HeckeRing.GLn
