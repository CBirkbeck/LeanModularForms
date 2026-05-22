/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.GLn.DiagonalRepresentatives
import LeanModularForms.HeckeRIngs.GLn.SLnTransvection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication

/-!
# Block Embedding Bijection for Hecke Multiplicities

Shimura's Lemma 3.19: the Hecke multiplicity at block-embedded cosets in
dimension `m+1` equals the multiplicity in dimension `m`.

## Proof infrastructure

### Stabilizer invariance

The stabilizer subgroup `H ∩ gHg⁻¹` is invariant under right multiplication
by `H` (`stabilizerSubgroup_mul_right_H`), and transforms by conjugation under
left multiplication (`stab_mul_left_eq_map_conj`).

### Conjugation equivalence on decompQuots

For `h ∈ H`, left multiplication `g ↦ h·g` conjugates the stabilizer:
`Stab(h·g) = h · Stab(g) · h⁻¹`. The quotient map `σ ↦ h⁻¹·σ·h` gives
`decompQuot(h·g) ≃ decompQuot(g)`. Combined with right-invariance, we get
`decompQuot(h·g·k) ≃ decompQuot(g)` for `h, k ∈ H`.

### Dimension reduction

The block embedding `diag(1, d) = 1 ⊕ diag(d)` induces
`decompQuot(m+1, diag(1,d)) ≃ decompQuot(m, diag(d))` via block projection
(Shimura Proposition 3.15).

### Coset helpers

- `singleton_mul_H_absorb_right`: `{a·c}·H = {a}·H` when `c ∈ H`
- `decompQuot_coset_indep'`: quotient class determines left coset
- `decompQuot_out_coset_eq'`: out-representative gives the same coset

## References

* Shimura, §3.2, Lemma 3.19, Proposition 3.15
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing

/-! ### Stabilizer subgroup invariance -/

section StabilizerInvariance

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Right multiplication by `h ∈ H` does not change the stabilizer subgroup:
`Stab(g·h) = Stab(g)` when `h ∈ H`, because `(g·h)H(g·h)⁻¹ = g(hHh⁻¹)g⁻¹ = gHg⁻¹`. -/
lemma stabilizerSubgroup_mul_right_H (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((g : G) * (h : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx
    have key : (g : G)⁻¹ * (x : G) * g =
        (h : G) * (((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G))) * (h : G)⁻¹ := by
      group
    rw [key]; exact P.H.mul_mem (P.H.mul_mem h.2 hx) (P.H.inv_mem h.2)
  · intro hx
    have key : ((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G)) =
        (h : G)⁻¹ * ((g : G)⁻¹ * (x : G) * (g : G)) * (h : G) := by group
    rw [key]; exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) hx) h.2

/-- Left multiplication by `h ∈ H` conjugates the stabilizer:
`Stab(h·g) = conj(h)(Stab(g))` as subgroups of `H`.
Concretely, `x ∈ Stab(h·g)` iff `h⁻¹·x·h ∈ Stab(g)`. -/
lemma stab_mul_left_eq_map_conj (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((h : G) * (g : G)) • P.H).subgroupOf P.H =
    ((ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H).map
      (MulAut.conj h).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨⟨(h : G)⁻¹ * (x : G) * (h : G),
      P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) x.2) h.2⟩, ?_, ?_⟩
    · show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) ∈ P.H
      rw [show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) =
        ((h : G) * (g : G))⁻¹ * (x : G) * ((h : G) * (g : G)) from by
        rw [_root_.mul_inv_rev]; simp [mul_assoc]]
      exact hx
    · ext; show (h : G) * ((h : G)⁻¹ * (x : G) * (h : G)) * (h : G)⁻¹ = (x : G)
      simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    show ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * (g : G)) ∈ P.H
    rw [show ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * (g : G)) =
      (g : G)⁻¹ * (y : G) * (g : G) from by
      rw [_root_.mul_inv_rev]; simp [mul_assoc]]
    exact hy

end StabilizerInvariance

/-! ### Conjugation equivalence on decompQuots -/

section ConjugationEquiv

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Conjugation by `h ∈ H` gives an Equiv on decomposition quotients:
`H/Stab(h·g) ≃ H/Stab(g)` via `σ ↦ h⁻¹·σ·h`.

The well-definedness uses `Stab(h·g) = h·Stab(g)·h⁻¹`, which means
`σ₁ ~_{Stab(h·g)} σ₂` iff `h⁻¹·σ₁·h ~_{Stab(g)} h⁻¹·σ₂·h`. -/
noncomputable def decompQuot_mul_left_equiv (g : P.Δ) (h : P.H)
    (hm : (h : G) * (g : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * g, hm⟩ ≃ decompQuot P g := by
  set K := (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H
  set K' := K.map (MulAut.conj h).toMonoidHom
  refine (Subgroup.quotientEquivOfEq (stab_mul_left_eq_map_conj P g h)).trans ?_
  have h_wd : ∀ a b : P.H, QuotientGroup.leftRel K' a b →
      QuotientGroup.leftRel K ((MulAut.conj h⁻¹) a) ((MulAut.conj h⁻¹) b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [show ((MulAut.conj h⁻¹) a)⁻¹ * (MulAut.conj h⁻¹) b =
      (MulAut.conj h⁻¹) (a⁻¹ * b) by simp [map_inv, map_mul]]
    rw [Subgroup.mem_map] at hab; obtain ⟨k, hk, hkeq⟩ := hab
    show (MulAut.conj h⁻¹) (a⁻¹ * b) ∈ K
    have : a⁻¹ * b = (MulAut.conj h) k := hkeq.symm
    rw [this]; convert hk using 1; ext; simp [MulAut.conj_apply, mul_assoc]
  exact Equiv.ofBijective
    (Quotient.map' (MulAut.conj h⁻¹) h_wd)
    ⟨fun x y hxy ↦ by
      revert x y; exact Quotient.ind₂ fun a b hxy ↦ by
        simp only [Quotient.map'_mk''] at hxy
        rw [Quotient.eq''] at hxy ⊢
        rw [QuotientGroup.leftRel_apply] at hxy ⊢
        rw [show ((MulAut.conj h⁻¹) a)⁻¹ * (MulAut.conj h⁻¹) b =
          (MulAut.conj h⁻¹) (a⁻¹ * b) by simp [map_inv, map_mul]] at hxy
        rw [Subgroup.mem_map]
        exact ⟨(MulAut.conj h⁻¹) (a⁻¹ * b), hxy, by
          ext; simp [MulAut.conj_apply, mul_assoc]⟩,
    fun x ↦ by
      revert x; exact Quotient.ind fun b ↦ ⟨Quotient.mk'' ((MulAut.conj h) b), by
        simp only [Quotient.map'_mk'']; rw [Quotient.eq'', QuotientGroup.leftRel_apply]
        rw [show ((MulAut.conj h⁻¹) ((MulAut.conj h) b))⁻¹ * b =
          1 by ext; simp [MulAut.conj_apply, mul_assoc]]
        exact K.one_mem⟩⟩

/-- Combined left-right invariance: `decompQuot(h·g·k) ≃ decompQuot(g)` for `h, k ∈ H`.
Composes right-invariance (stabilizer equality) with left-conjugation. -/
noncomputable def decompQuot_double_H_equiv (g : P.Δ) (h k : P.H)
    (hm : (h : G) * (g : G) * (k : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * (g : G) * (k : G), hm⟩ ≃ decompQuot P g := by
  have hgk : (g : G) * (k : G) ∈ P.Δ := P.Δ.mul_mem g.2 (P.h₀ k.2)
  have hhgk : (h : G) * ((g : G) * (k : G)) ∈ P.Δ := by rwa [mul_assoc] at hm
  refine (Subgroup.quotientEquivOfEq ?_).trans
    ((decompQuot_mul_left_equiv P ⟨(g : G) * k, hgk⟩ h hhgk).trans
    (Subgroup.quotientEquivOfEq (stabilizerSubgroup_mul_right_H P g k)))
  show (ConjAct.toConjAct ((h : G) * (g : G) * (k : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct ((h : G) * ((g : G) * (k : G))) • P.H).subgroupOf P.H
  congr 2; exact mul_assoc _ _ _

end ConjugationEquiv

/-! ### Coset manipulation helpers -/

section CosetHelpers

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Right-multiplying by an H-element doesn't change the right coset `{a} * H`. -/
lemma singleton_mul_H_absorb_right (a c : G) (hc : c ∈ P.H) :
    ({a * c} : Set G) * (P.H : Set G) = ({a} : Set G) * (P.H : Set G) := by
  ext x; constructor
  · rintro ⟨_, rfl, k, hk, rfl⟩; exact ⟨_, rfl, c * k, P.H.mul_mem hc hk, by group⟩
  · rintro ⟨_, rfl, k, hk, rfl⟩
    exact ⟨_, rfl, c⁻¹ * k, P.H.mul_mem (P.H.inv_mem hc) hk, by group⟩

/-- If two `H`-elements are in the same `decompQuot` class for `g`, they give the same
left coset `{σ * g} * H`. -/
lemma decompQuot_coset_indep' (g : P.Δ)
    (x y : P.H) (hxy : (⟦x⟧ : decompQuot P g) = ⟦y⟧) :
    ({(x : G) * (g : G)} : Set G) * (P.H : Set G) =
    {(y : G) * (g : G)} * (P.H : Set G) := by
  rw [Quotient.eq''] at hxy
  change (QuotientGroup.leftRel _) x y at hxy
  rw [QuotientGroup.leftRel_apply] at hxy
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at hxy
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv] at hxy
  have hxy' : (g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G) ∈ P.H := by
    convert hxy using 1; group
  ext z; simp only [Set.singleton_mul, Set.image_mul_left, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro hz
    show ((y : G) * (g : G))⁻¹ * z ∈ P.H
    have key : ((y : G) * (g : G))⁻¹ * z =
        ((g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G))⁻¹ *
        (((x : G) * (g : G))⁻¹ * z) := by group
    rw [key]; exact P.H.mul_mem (P.H.inv_mem hxy') hz
  · intro hz
    show ((x : G) * (g : G))⁻¹ * z ∈ P.H
    have key : ((x : G) * (g : G))⁻¹ * z =
        ((g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G)) *
        (((y : G) * (g : G))⁻¹ * z) := by group
    rw [key]; exact P.H.mul_mem hxy' hz

/-- The `out` representative of a quotient element gives the same coset as the original. -/
lemma decompQuot_out_coset_eq' (g : P.Δ) (x : P.H) :
    ({((⟦x⟧ : decompQuot P g).out : G) * (g : G)} : Set G) * (P.H : Set G) =
    {(x : G) * (g : G)} * (P.H : Set G) :=
  decompQuot_coset_indep' P g (⟦x⟧ : decompQuot P g).out x (Quotient.out_eq _)

end CosetHelpers

end HeckeRing

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

/-! ### Block embedding helpers for `slSuccEmbed`

The block embedding `SL_{k+1}(Z) → SL_{k+2}(Z)` via `M ↦ 1 ⊕ M` is defined as
`slSuccEmbed`. We prove it is a monoid homomorphism and preserves stabilizers. -/

section SlSuccEmbedHelpers

/-- Block embedding `SL_{k+1}(ℤ) → SL_{k+2}(ℤ)` via `M ↦ 1 ⊕ M`. -/
private noncomputable def slSuccEmbed {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  let e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  refine ⟨(fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).submatrix e e, ?_⟩
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, one_mul, M.prop]

/-- The matrix underlying `slSuccEmbed M` equals `(fromBlocks 1 0 0 M).submatrix e e`
for `e = castOrderIso ∘ finSumFinEquiv⁻¹`. This is definitionally true but useful
as a rewrite lemma to unify different copies of the `let`-bound `fin1Sum`. -/
private lemma slSuccEmbed_val_eq {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    (slSuccEmbed M).1 = (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
      (M : Matrix _ _ ℤ)).submatrix
      (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
        |>.toEquiv.trans finSumFinEquiv.symm)
      (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
        |>.toEquiv.trans finSumFinEquiv.symm) := rfl

set_option maxHeartbeats 800000 in
/-- `slSuccEmbed` is multiplicative: `(1 ⊕ A) · (1 ⊕ B) = 1 ⊕ (A · B)`. -/
private lemma slSuccEmbed_mul {k : ℕ} (A B : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slSuccEmbed (A * B) = slSuccEmbed A * slSuccEmbed B := by
  apply Subtype.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  have lhs : (slSuccEmbed (A * B)).1 =
    (fromBlocks 1 0 0 ((A : Matrix _ _ ℤ) * (B : Matrix _ _ ℤ))).submatrix e e := by
    rw [slSuccEmbed_val_eq]; ext i j
    simp only [SpecialLinearGroup.coe_mul, submatrix_apply]; rfl
  have rhs : (slSuccEmbed A * slSuccEmbed B).1 =
    (fromBlocks 1 0 0 (A : Matrix _ _ ℤ)).submatrix e e *
    (fromBlocks 1 0 0 (B : Matrix _ _ ℤ)).submatrix e e := by
    simp only [SpecialLinearGroup.coe_mul]; rw [slSuccEmbed_val_eq, slSuccEmbed_val_eq]
  rw [lhs, rhs,
    show fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 ((A.1) * (B.1)) =
      fromBlocks 1 0 0 A.1 * fromBlocks 1 0 0 B.1 from by
      rw [fromBlocks_multiply]; simp]
  exact (submatrix_mul_equiv _ _ e e e).symm

/-- `slSuccEmbed 1 = 1`: the identity embeds as the identity. -/
private lemma slSuccEmbed_one {k : ℕ} :
    slSuccEmbed (1 : SpecialLinearGroup (Fin (k + 1)) ℤ) = 1 := by
  apply Subtype.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  rw [slSuccEmbed_val_eq]; simp only [SpecialLinearGroup.coe_one, fromBlocks_one]
  ext i j; simp only [submatrix_apply, one_apply, Equiv.apply_eq_iff_eq]

/-- `slSuccEmbed` preserves inverses. -/
private lemma slSuccEmbed_inv {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slSuccEmbed M⁻¹ = (slSuccEmbed M)⁻¹ := by
  apply mul_left_cancel (a := slSuccEmbed M)
  rw [mul_inv_cancel, ← slSuccEmbed_mul, mul_inv_cancel, slSuccEmbed_one]

/-- Extract the SL preimage of an element of `(GL_pair n).H = SLnZ_subgroup n`. -/
private noncomputable def toSL {n : ℕ} [NeZero n] (σ : (GL_pair n).H) :
    SpecialLinearGroup (Fin n) ℤ :=
  (Classical.indefiniteDescription _ σ.2).val

private lemma toSL_spec {n : ℕ} [NeZero n] (σ : (GL_pair n).H) :
    mapGL ℚ (toSL σ) = (σ : GL (Fin n) ℚ) :=
  (Classical.indefiniteDescription _ σ.2).prop

/-- `mapGL ℚ` is injective on `SpecialLinearGroup`. -/
private lemma mapGL_injective (n : ℕ) :
    Function.Injective
      (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ) := by
  intro a b h
  have h_mat : (a : Matrix (Fin n) (Fin n) ℤ) = (b : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    have hij := congr_arg (fun g ↦ (g : Matrix (Fin n) (Fin n) ℚ) i j)
      (show (mapGL ℚ a : Matrix _ _ ℚ) = (mapGL ℚ b : Matrix _ _ ℚ) from
        congr_arg Units.val h)
    simp only [mapGL_coe_matrix, algebraMap_int_eq] at hij
    exact Int.cast_injective hij
  exact Subtype.ext h_mat

/-! ### H-level block embedding

The block embedding `σ ↦ 1 ⊕ σ` lifted to the Hecke pair subgroups
`(GL_pair (k+1)).H → (GL_pair (k+2)).H`. This is the main piece of reusable
local API for the block-bijection proof. -/

/-- Lift `slSuccEmbed` to the Hecke pair subgroup: `(GL_pair (k+1)).H → (GL_pair (k+2)).H`. -/
private noncomputable def slSuccEmbed_H {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    (GL_pair (k + 2)).H := by
  refine ⟨mapGL ℚ (slSuccEmbed (toSL σ)), ?_⟩
  show (mapGL ℚ (slSuccEmbed (toSL σ)) : GL (Fin (k + 2)) ℚ) ∈ SLnZ_subgroup (k + 2)
  rw [MonoidHom.mem_range]
  exact ⟨slSuccEmbed (toSL σ), rfl⟩

/-- The underlying `GL` value of `slSuccEmbed_H σ` equals `mapGL ℚ (slSuccEmbed (toSL σ))`. -/
private lemma slSuccEmbed_H_val {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) = mapGL ℚ (slSuccEmbed (toSL σ)) := rfl

/-- `slSuccEmbed_H` is multiplicative on the H level. -/
private lemma slSuccEmbed_H_mul {k : ℕ} (σ₁ σ₂ : (GL_pair (k + 1)).H) :
    slSuccEmbed_H (σ₁ * σ₂) = slSuccEmbed_H σ₁ * slSuccEmbed_H σ₂ := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL (σ₁ * σ₂))) : GL _ ℚ) =
    (mapGL ℚ (slSuccEmbed (toSL σ₁)) : GL _ ℚ) * mapGL ℚ (slSuccEmbed (toSL σ₂))
  have htoSL : toSL (σ₁ * σ₂) = toSL σ₁ * toSL σ₂ := by
    apply mapGL_injective (k + 1)
    rw [map_mul, toSL_spec, toSL_spec, toSL_spec]
    exact Subgroup.coe_mul _ _ _
  rw [htoSL, slSuccEmbed_mul, map_mul]

/-- `slSuccEmbed_H` sends `1` to `1`. -/
private lemma slSuccEmbed_H_one {k : ℕ} :
    slSuccEmbed_H (1 : (GL_pair (k + 1)).H) = 1 := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL 1)) : GL _ ℚ) = 1
  have htoSL : toSL (1 : (GL_pair (k + 1)).H) = 1 :=
    mapGL_injective (k + 1) (by rw [toSL_spec]; simp [map_one])
  rw [htoSL, slSuccEmbed_one, map_one]

/-- `slSuccEmbed` is injective as a map `SL(k+1) → SL(k+2)`. -/
private lemma slSuccEmbed_injective {k : ℕ} :
    Function.Injective (slSuccEmbed : SpecialLinearGroup (Fin (k + 1)) ℤ →
      SpecialLinearGroup (Fin (k + 2)) ℤ) := by
  intro A B h
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  have hSub : (slSuccEmbed A).1 = (slSuccEmbed B).1 := congr_arg Subtype.val h
  rw [slSuccEmbed_val_eq, slSuccEmbed_val_eq] at hSub
  have hFromBlocks :
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 A.1) = fromBlocks 1 0 0 B.1 := by
    have hSub' := congr_arg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦
      M.submatrix e.symm e.symm) hSub
    simp only at hSub'
    have h1 : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 A.1) =
        ((fromBlocks 1 0 0 A.1).submatrix e e).submatrix e.symm e.symm := by
      simp [submatrix_submatrix, Equiv.self_comp_symm]
    have h2 : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 B.1) =
        ((fromBlocks 1 0 0 B.1).submatrix e e).submatrix e.symm e.symm := by
      simp [submatrix_submatrix, Equiv.self_comp_symm]
    rw [h1, h2, hSub']
  have hAB : A.1 = B.1 := by
    have := congr_arg Matrix.toBlocks₂₂ hFromBlocks
    simpa [toBlocks_fromBlocks₂₂] using this
  exact Subtype.ext hAB

/-- `slSuccEmbed_H` preserves inverses: `slSuccEmbed_H σ⁻¹ = (slSuccEmbed_H σ)⁻¹`. -/
private lemma slSuccEmbed_H_inv {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    slSuccEmbed_H σ⁻¹ = (slSuccEmbed_H σ)⁻¹ := by
  apply mul_left_cancel (a := slSuccEmbed_H σ)
  rw [mul_inv_cancel, ← slSuccEmbed_H_mul, mul_inv_cancel, slSuccEmbed_H_one]

/-- `slSuccEmbed_H` is injective. -/
private lemma slSuccEmbed_H_injective {k : ℕ} :
    Function.Injective (slSuccEmbed_H : (GL_pair (k + 1)).H → (GL_pair (k + 2)).H) := by
  intro σ₁ σ₂ h
  have hval : (slSuccEmbed_H σ₁ : GL (Fin (k + 2)) ℚ) =
      (slSuccEmbed_H σ₂ : GL (Fin (k + 2)) ℚ) :=
    congr_arg (fun x : (GL_pair (k + 2)).H ↦ (x : GL (Fin (k + 2)) ℚ)) h
  rw [slSuccEmbed_H_val, slSuccEmbed_H_val] at hval
  have hSL : slSuccEmbed (toSL σ₁) = slSuccEmbed (toSL σ₂) :=
    mapGL_injective (k + 2) hval
  have htoSL : toSL σ₁ = toSL σ₂ := slSuccEmbed_injective hSL
  apply Subtype.ext
  rw [← toSL_spec σ₁, ← toSL_spec σ₂, htoSL]

end SlSuccEmbedHelpers

/-! ### Dimension reduction: decompQuot(m+1, rep(T(1,d))) ≃ decompQuot(m, rep(T(d)))

The Equiv chains three steps:
1. `decompQuot(rep(T(1,d))) ≃ decompQuot(diagMat(1,d))` via H-conjugation
   (using `T_diag_rep_decompose` + `decompQuot_double_H_equiv`)
2. `decompQuot(m+1, diagMat(1,d)) ≃ decompQuot(m, diagMat(d))` via block projection
   (Shimura Prop 3.15: the stabilizer for diagonal matrices has block structure)
3. `decompQuot(diagMat(d)) ≃ decompQuot(rep(T(d)))` via reverse H-conjugation
-/

omit [NeZero m] in
/-- The block conjugation identity: conjugating a block-embedded matrix `1 ⊕ M` by
`diag(1, d₁, ..., dₖ)` yields `1 ⊕ (diag(d)⁻¹ · M · diag(d))`.
This gives: if `diag(d)⁻¹ * mapGL(M) * diag(d) = mapGL(N)`, then
`diag(1,d)⁻¹ * mapGL(slSuccEmbed(M)) * diag(1,d) = mapGL(slSuccEmbed(N))`. -/
private lemma block_conj_identity {k : ℕ}
    (d : Fin (k + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (M N : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (hMN : (diagMat (k + 1) d)⁻¹ * mapGL ℚ M * diagMat (k + 1) d = mapGL ℚ N) :
    (diagMat (k + 2) (Fin.cons 1 d))⁻¹ * mapGL ℚ (slSuccEmbed M) *
      diagMat (k + 2) (Fin.cons 1 d) = mapGL ℚ (slSuccEmbed N) := by
  have hcons_pos : ∀ i : Fin (k + 2), 0 < (Fin.cons 1 d : Fin (k + 2) → ℕ) i := by
    intro i; refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [Fin.cons_zero]
    · rw [Fin.cons_succ]; exact hd j
  set D' := diagMat (k + 2) (Fin.cons 1 d) with hD'_def
  set D := diagMat (k + 1) d with hD_def
  have hMN_mul : mapGL ℚ M * D = D * mapGL ℚ N := by
    have h1 := congr_arg (D * ·) hMN
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at h1
    exact h1
  suffices hmul : mapGL ℚ (slSuccEmbed M) * D' = D' * mapGL ℚ (slSuccEmbed N) by
    have h1 := congr_arg (D'⁻¹ * ·) hmul
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact h1
  apply Units.ext; ext i j
  simp only [Units.val_mul, mul_apply, hD'_def, diagMat_val _ _ hcons_pos, diagonal_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  all_goals simp only [mapGL_coe_matrix, algebraMap_int_eq, Fin.cons_zero, Fin.cons_succ,
    Nat.cast_one]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · have h4 := congr_arg Units.val hMN_mul
    simp only [Units.val_mul] at h4
    have h4_entry := congr_fun (congr_fun h4 i') j'
    simp only [hD_def, diagMat_val _ _ hd, mul_apply, diagonal_apply, mul_ite, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at h4_entry
    convert h4_entry using 2 <;>
      simp [mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.map,
        RingHom.mapMatrix_apply, Matrix.map_apply, slSuccEmbed_val_eq,
        submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso,
        finSumFinEquiv, Fin.addCases, Fin.subNat]

/-- **Stabilizer preservation for `slSuccEmbed_H` at the diagMat level.**
If `σ ∈ H_{k+1}` satisfies the conjugation stabilizer condition for `diagMat(a)`
(i.e., `diagMat(a)⁻¹ σ diagMat(a) ∈ H_{k+1}`), then `slSuccEmbed_H σ ∈ H_{k+2}`
satisfies the analogous condition for `diagMat(cons 1 a)`. This is the key
tool for lifting `decompQuot` classes through the block embedding. -/
private lemma slSuccEmbed_H_stab_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (hσ : (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a ∈
        (GL_pair (k + 1)).H) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨ν, hν⟩ := hσ
  have h_hyp : (diagMat (k + 1) a)⁻¹ * mapGL ℚ (toSL σ) * diagMat (k + 1) a =
      mapGL ℚ ν := by
    rw [toSL_spec σ]; exact hν.symm
  have h_block := block_conj_identity a ha (toSL σ) ν h_hyp
  rw [slSuccEmbed_H_val]
  exact ⟨slSuccEmbed ν, h_block.symm⟩


/-- Positivity lifts through `Fin.cons 1`: if every `a i` is positive, so is every
`(Fin.cons 1 a) i`. Local helper for diagonal block embedding. -/
private lemma cons_one_pos {k : ℕ} {a : Fin (k + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∀ i : Fin (k + 2), 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) i := by
  intro i; refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Fin.cons_zero]
  · rw [Fin.cons_succ]; exact ha j

/-- **Sufficient direction for diag-conjugation membership.** If the integer matrix
`N ∈ SL(k+2, ℤ)` satisfies the entry-wise divisibility
`(Fin.cons 1 a) i ∣ N i j * (Fin.cons 1 a) j` for all `i j`, then the conjugate
`D⁻¹ * mapGL ℚ N * D` lies in `SL_{k+2}(ℤ)` viewed as a subgroup of `GL_{k+2}(ℚ)`,
where `D := diagMat (Fin.cons 1 a)`.

The witness integer matrix `M ∈ SL(k+2, ℤ)` has entries
`M i j = (N i j * (cons 1 a j)) / (cons 1 a i)` (integer division, exact by
hypothesis). -/
private lemma diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd
    {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_dvd : ∀ i j : Fin (k + 2),
      ((Fin.cons 1 a : Fin (k + 2) → ℕ) i : ℤ) ∣
        N.1 i j * ((Fin.cons 1 a : Fin (k + 2) → ℕ) j : ℤ)) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  set c : Fin (k + 2) → ℕ := Fin.cons 1 a with hc_def
  have hc_pos : ∀ i, 0 < c i := cons_one_pos ha
  have hc_ne : ∀ i, ((c i : ℤ) : ℚ) ≠ 0 := by
    intro i
    exact_mod_cast (hc_pos i).ne'
  have hc_int_ne : ∀ i, (c i : ℤ) ≠ 0 := fun i ↦ by exact_mod_cast (hc_pos i).ne'
  let Mraw : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    fun i j ↦ (N.1 i j * (c j : ℤ)) / (c i : ℤ)
  set D : GL (Fin (k + 2)) ℚ := diagMat (k + 2) c with hD_def
  have h_entry_cast : ∀ i j,
      (Mraw i j : ℚ) * (c i : ℤ) = (N.1 i j : ℚ) * (c j : ℤ) := by
    intro i j
    have hdvd := h_dvd i j
    have hmul : (Mraw i j) * (c i : ℤ) = N.1 i j * (c j : ℤ) := by
      simp only [Mraw]
      rw [Int.ediv_mul_cancel hdvd]
    have := congr_arg (fun z : ℤ ↦ (z : ℚ)) hmul
    push_cast at this
    convert this using 1
  have h_mat_eq :
      (mapGL ℚ N : Matrix _ _ ℚ) * (D : Matrix _ _ ℚ) =
        (D : Matrix _ _ ℚ) * (Mraw.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    simp only [hD_def, diagMat_val _ _ hc_pos, mul_apply, diagonal_apply, mul_ite,
      mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mapGL_coe_matrix, algebraMap_int_eq]
    show ((N.1 i j : ℤ) : ℚ) * (c j : ℚ) = (c i : ℚ) * ((Mraw i j : ℤ) : ℚ)
    have he := h_entry_cast i j
    have hci : (((c i : ℤ) : ℚ)) = (c i : ℚ) := by push_cast; ring
    have hcj : (((c j : ℤ) : ℚ)) = (c j : ℚ) := by push_cast; ring
    rw [hci, hcj] at he
    linarith [he]
  have hD_det_ne : (D.val).det ≠ 0 := by
    have : (D.val).det = ∏ i, (c i : ℚ) := by
      simp [hD_def, diagMat_det _ _ hc_pos]
    rw [this]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hc_ne i)
  have h_detM_cast : (Mraw.map (Int.cast : ℤ → ℚ)).det = 1 := by
    have hdet := congr_arg Matrix.det h_mat_eq
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hN1 : ((mapGL ℚ N).val).det = 1 := by
      have h1 : ((mapGL ℚ N).val).det = (N.val.map (Int.cast : ℤ → ℚ)).det := by
        rw [mapGL_coe_matrix]
        simp [algebraMap_int_eq]
      rw [h1, ← Int.cast_det, N.2]; simp
    rw [hN1, one_mul] at hdet
    have hdet' : (D.val).det * (Mraw.map (Int.cast : ℤ → ℚ)).det = (D.val).det * 1 := by
      rw [mul_one]; linarith [hdet]
    exact mul_left_cancel₀ hD_det_ne hdet'
  have h_detM_int : Mraw.det = 1 := by
    have hcast : ((Mraw.det : ℤ) : ℚ) = (Mraw.map (Int.cast : ℤ → ℚ)).det :=
      Int.cast_det Mraw
    have : ((Mraw.det : ℤ) : ℚ) = (1 : ℚ) := by rw [hcast]; exact h_detM_cast
    exact_mod_cast this
  let M : SpecialLinearGroup (Fin (k + 2)) ℤ := ⟨Mraw, h_detM_int⟩
  refine ⟨M, ?_⟩
  have h_mapGL_M_mat : ((mapGL ℚ M : Matrix _ _ ℚ)) = Mraw.map (Int.cast : ℤ → ℚ) := by
    rw [mapGL_coe_matrix]; rfl
  have h_units : (mapGL ℚ N : GL (Fin (k + 2)) ℚ) * D = D * mapGL ℚ M := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, h_mapGL_M_mat]
    exact h_mat_eq
  have h_target : D⁻¹ * (mapGL ℚ N : GL (Fin (k + 2)) ℚ) * D = mapGL ℚ M := by
    have h1 := congr_arg (D⁻¹ * ·) h_units
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact h1
  exact h_target.symm



/-- **The block-embedding map on `decompQuot` at the `diagMat_delta` level.**
Given a positive diagonal `a`, `slSuccEmbed_H` descends from `H_{k+1}` to a well-defined
map between `decompQuot (GL_pair (k+1)) (diagMat_delta (k+1) a)` and
`decompQuot (GL_pair (k+2)) (diagMat_delta (k+2) (Fin.cons 1 a))`. Well-definedness is
provided by `slSuccEmbed_H_stab_diagMat` combined with `slSuccEmbed_H_mul/_inv`. -/
private noncomputable def decompQuot_slSuccEmbed_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) →
    decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) := by
  refine Quotient.map' slSuccEmbed_H ?_
  intro σ₁ σ₂ h_rel
  rw [QuotientGroup.leftRel_apply] at h_rel ⊢
  have h_mul : (slSuccEmbed_H σ₁)⁻¹ * slSuccEmbed_H σ₂ =
      slSuccEmbed_H (σ₁⁻¹ * σ₂) := by
    rw [← slSuccEmbed_H_inv, ← slSuccEmbed_H_mul]
  rw [h_mul]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h_rel ⊢
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_rel ⊢
  rw [show ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) : GL (Fin (k + 1)) ℚ) =
        diagMat (k + 1) a from diagMat_delta_val (k + 1) a ha] at h_rel
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)]
  exact slSuccEmbed_H_stab_diagMat a ha (σ₁⁻¹ * σ₂) h_rel

/-! ### Block entry extraction lemmas for `slSuccEmbed`

These four unfold `(slSuccEmbed τ).val` at the four block quadrants of
`Fin (k + 2) = {0} ⊕ Fin (k + 1)`, matching the `1 ⊕ τ` structure. They are
local simp-style helpers used in the converse stabilizer lemma. -/

private lemma slSuccEmbed_val_zero_zero {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    (slSuccEmbed τ).val 0 0 = 1 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

private lemma slSuccEmbed_val_zero_succ {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (j : Fin (k + 1)) :
    (slSuccEmbed τ).val 0 j.succ = 0 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

private lemma slSuccEmbed_val_succ_zero {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (i : Fin (k + 1)) :
    (slSuccEmbed τ).val i.succ 0 = 0 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

private lemma slSuccEmbed_val_succ_succ {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (i j : Fin (k + 1)) :
    (slSuccEmbed τ).val i.succ j.succ = τ.val i j := by
  rw [slSuccEmbed_val_eq]
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]
  simp [Fin.subNat]

/-- Flipped form of the conjugation equation: move `D₂` to the right-hand side to
avoid dealing with its inverse during entry extraction. -/
private lemma slSuccEmbed_conj_flip {k : ℕ}
    (a : Fin (k + 1) → ℕ)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hν : mapGL ℚ ν = (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a)) :
    (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν := by
  rw [hν]; group

/-- Entry-wise consequence of the flipped conjugation equation: for every pair of
indices `i j : Fin (k + 2)`,
`(slSuccEmbed (toSL σ)).val i j · (Fin.cons 1 a) j = (Fin.cons 1 a) i · ν.val i j`
holds at the rational level. -/
private lemma slSuccEmbed_conj_entry {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i j : Fin (k + 2)) :
    ((slSuccEmbed (toSL σ)).val i j : ℚ) * ((Fin.cons 1 a : Fin (k + 2) → ℕ) j : ℚ) =
      ((Fin.cons 1 a : Fin (k + 2) → ℕ) i : ℚ) * (ν.val i j : ℚ) := by
  have hcons_pos := cons_one_pos ha
  have h := congr_arg (fun (x : GL (Fin (k + 2)) ℚ) ↦ (x : Matrix _ _ ℚ) i j) hflip
  simp only [Units.val_mul, Matrix.mul_apply, slSuccEmbed_H_val,
             mapGL_coe_matrix, algebraMap_int_eq, diagMat_val _ _ hcons_pos,
             Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
             Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
             SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
             Matrix.map_apply] at h
  exact h

/-- From the entry equation, the top-left entry of `ν` is `1`. -/
private lemma slSuccEmbed_conj_ν_zero_zero {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    ν.val 0 0 = 1 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip 0 0
  rw [slSuccEmbed_val_zero_zero] at h
  simp only [Fin.cons_zero, Nat.cast_one, mul_one, one_mul] at h
  exact_mod_cast h.symm

/-- From the entry equation, the first-row entries (beyond `0 0`) of `ν` are `0`. -/
private lemma slSuccEmbed_conj_ν_zero_succ {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (j : Fin (k + 1)) :
    ν.val 0 j.succ = 0 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip 0 j.succ
  rw [slSuccEmbed_val_zero_succ] at h
  simp only [Int.cast_zero, zero_mul, Fin.cons_zero, Nat.cast_one, one_mul] at h
  exact_mod_cast h.symm

/-- From the entry equation, the first-column entries (beyond `0 0`) of `ν` are `0`. -/
private lemma slSuccEmbed_conj_ν_succ_zero {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i : Fin (k + 1)) :
    ν.val i.succ 0 = 0 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip i.succ 0
  rw [slSuccEmbed_val_succ_zero] at h
  simp only [Int.cast_zero, Fin.cons_zero, Nat.cast_one, mul_one, Fin.cons_succ] at h
  have hai : (0 : ℚ) < (a i : ℚ) := by exact_mod_cast ha i
  have hν_zero : (ν.val i.succ 0 : ℚ) = 0 := by
    have h' : (a i : ℚ) * (ν.val i.succ 0 : ℚ) = 0 := h.symm
    exact (mul_eq_zero.mp h').resolve_left hai.ne'
  exact_mod_cast hν_zero

/-- Entry relation for the bottom-right `(k+1) × (k+1)` block: at position
`(i.succ, j.succ)`, the identity `(toSL σ).val i j · a j = a i · ν.val i.succ j.succ`
holds at the rational level. -/
private lemma slSuccEmbed_conj_ν_succ_succ {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i j : Fin (k + 1)) :
    ((toSL σ).val i j : ℚ) * (a j : ℚ) = (a i : ℚ) * (ν.val i.succ j.succ : ℚ) := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip i.succ j.succ
  rw [slSuccEmbed_val_succ_succ] at h
  simp only [Fin.cons_succ] at h
  exact h

/-- Determinant of the bottom-right block: with `ν.val 0 0 = 1` and zero first
column (`ν.val i.succ 0 = 0`), cofactor expansion along column `0` collapses to
the bottom-right `(k+1) × (k+1)` block's determinant, which equals `det ν = 1`. -/
private lemma ν_bottomBlock_det {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    Matrix.det (M := (fun i j : Fin (k + 1) ↦ ν.val i.succ j.succ :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)) = 1 := by
  set ν'_mat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j ↦ ν.val i.succ j.succ with hν'_mat_def
  have h00 := slSuccEmbed_conj_ν_zero_zero a ha σ ν hflip
  have h_col : ∀ i : Fin (k + 1), ν.val i.succ 0 = 0 :=
    fun i ↦ slSuccEmbed_conj_ν_succ_zero a ha σ ν hflip i
  have h_expand := Matrix.det_succ_column ν.val 0
  rw [Fin.sum_univ_succ] at h_expand
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, h00] at h_expand
  have h_zero_sum :
      (∑ x : Fin (k + 1), (-1 : ℤ) ^ (x.succ : Fin (k + 2)).val * ν.val x.succ 0 *
        (ν.val.submatrix x.succ.succAbove (Fin.succAbove 0)).det) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [h_col]; ring
  rw [h_zero_sum, add_zero] at h_expand
  rw [ν.prop] at h_expand
  have h_sub : ν'_mat = ν.val.submatrix (Fin.succAbove 0) (Fin.succAbove 0) := by
    ext i j; simp only [hν'_mat_def, Matrix.submatrix_apply, Fin.succAbove_zero]
  show ν'_mat.det = 1
  rw [h_sub]
  exact h_expand.symm

/-- Package the bottom-right block of `ν` as an element of `SL_{k+1}(ℤ)`. -/
private noncomputable def ν_bottomBlock {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    SpecialLinearGroup (Fin (k + 1)) ℤ :=
  ⟨fun i j ↦ ν.val i.succ j.succ, ν_bottomBlock_det a ha σ ν hflip⟩

/-- The bottom-right block, mapped into `GL_{k+1}(ℚ)`, is the target of the conjugation
at dim `k + 1`: `mapGL ν_bottomBlock = (diagMat a)⁻¹ · σ · diagMat a`. Proof by
the entry-wise equation at `(i, j)` obtained from the dim-`k + 2` equation at
`(i.succ, j.succ)`. -/
private lemma ν_bottomBlock_mapGL_eq {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a =
      mapGL ℚ (ν_bottomBlock a ha σ ν hflip) := by
  have h_flip_k1 : (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a =
      diagMat (k + 1) a * mapGL ℚ (ν_bottomBlock a ha σ ν hflip) := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul, Matrix.mul_apply, diagMat_val _ _ ha,
               Matrix.diagonal_apply, mul_ite, ite_mul, zero_mul, mul_zero,
               Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
               mapGL_coe_matrix, algebraMap_int_eq,
               SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
               Matrix.map_apply]
    have h_σ : (σ : GL (Fin (k + 1)) ℚ).val i j = ((toSL σ).val i j : ℚ) := by
      have : mapGL ℚ (toSL σ) = σ := toSL_spec σ
      have h' := congr_arg (fun (x : GL _ ℚ) ↦ x.val i j) this
      simp only [mapGL_coe_matrix, algebraMap_int_eq,
                 SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
                 Matrix.map_apply] at h'
      exact h'.symm
    rw [h_σ]
    exact slSuccEmbed_conj_ν_succ_succ a ha σ ν hflip i j
  have : (diagMat (k + 1) a)⁻¹ * ((σ : GL _ ℚ) * diagMat (k + 1) a) =
      (diagMat (k + 1) a)⁻¹ * (diagMat (k + 1) a * mapGL ℚ (ν_bottomBlock a ha σ ν hflip)) :=
    congr_arg ((diagMat (k + 1) a)⁻¹ * ·) h_flip_k1
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at this
  exact this

/-- **Converse stabilizer preservation**: if `slSuccEmbed_H σ` lies in the conjugation
stabilizer of `diagMat(cons 1 a)` at dim `k+2`, then `σ` already lies in the stabilizer
of `diagMat(a)` at dim `k+1`. Proof extracts `ν : SL(k+2)` from the hypothesis,
uses the block-structure entry lemmas (`slSuccEmbed_conj_ν_zero_zero`,
`slSuccEmbed_conj_ν_zero_succ`, `slSuccEmbed_conj_ν_succ_zero`,
`slSuccEmbed_conj_ν_succ_succ`) and column-zero cofactor expansion to build an
`SL(k+1)` preimage `ν_bottomBlock` witnessing the dim-`k+1` stabilizer. -/
private lemma slSuccEmbed_H_stab_diagMat_converse {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (hσ' : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) ∈
      (GL_pair (k + 2)).H) :
    (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a ∈
      (GL_pair (k + 1)).H := by
  obtain ⟨ν, hν⟩ := hσ'
  have hflip := slSuccEmbed_conj_flip a σ ν hν
  exact ⟨ν_bottomBlock a ha σ ν hflip,
    (ν_bottomBlock_mapGL_eq a ha σ ν hflip).symm⟩

/-- The block-embedding map `decompQuot_slSuccEmbed_diagMat` is injective. Follows from
`slSuccEmbed_H_stab_diagMat_converse`: equality of `slSuccEmbed_H σ₁` and `slSuccEmbed_H σ₂`
modulo the dim-`k + 2` stabilizer forces `σ₁` and `σ₂` to be equal modulo the dim-`k + 1`
stabilizer. -/
private lemma decompQuot_slSuccEmbed_diagMat_injective {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    Function.Injective (decompQuot_slSuccEmbed_diagMat a ha) := by
  refine Quotient.ind₂ ?_
  intro σ₁ σ₂ h
  change (⟦slSuccEmbed_H σ₁⟧ : decompQuot _ _) = ⟦slSuccEmbed_H σ₂⟧ at h
  rw [Quotient.eq] at h
  change QuotientGroup.leftRel _ (slSuccEmbed_H σ₁) (slSuccEmbed_H σ₂) at h
  rw [QuotientGroup.leftRel_apply] at h
  have h_mul : (slSuccEmbed_H σ₁)⁻¹ * slSuccEmbed_H σ₂ =
      slSuccEmbed_H (σ₁⁻¹ * σ₂) := by
    rw [← slSuccEmbed_H_inv, ← slSuccEmbed_H_mul]
  rw [h_mul] at h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)] at h
  have h_stab := slSuccEmbed_H_stab_diagMat_converse a ha (σ₁⁻¹ * σ₂) h
  apply Quotient.sound
  change QuotientGroup.leftRel _ σ₁ σ₂
  rw [QuotientGroup.leftRel_apply,
      Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) : GL (Fin (k + 1)) ℚ) =
        diagMat (k + 1) a from diagMat_delta_val (k + 1) a ha]
  exact h_stab

/-! ### GL-level block embedding

A general block embedding `blockEmbedGL : GL_{k+1}(ℚ) → GL_{k+2}(ℚ)` via
`X ↦ fromBlocks 1 0 0 X` (with appropriate reindexing). This is multiplicative,
sends `diagMat (k+1) a` to `diagMat (k+2) (cons 1 a)`, and agrees with
`slSuccEmbed_H` on `H_{k+1}` as well as with `slSuccEmbed` on `SL_{k+1}(ℤ)` via
`mapGL`. The fiber-condition block transfer comes immediately from these rules. -/

/-- Block embedding of a GL element: `X ↦ (fromBlocks 1 0 0 X).submatrix e e`
for the standard equiv `e : Fin (k+2) ≃ Fin 1 ⊕ Fin (k+1)`. -/
private noncomputable def blockEmbedGL {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    GL (Fin (k + 2)) ℚ := by
  refine GeneralLinearGroup.mkOfDetNeZero
    ((Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)) ?_
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have h_det_prod : X.val.det * (X⁻¹ : GL (Fin (k + 1)) ℚ).val.det = 1 := by
    rw [← Matrix.det_mul]
    have h_mul : X.val * (X⁻¹ : GL _ ℚ).val = 1 := by exact_mod_cast X.mul_inv
    rw [h_mul]; exact Matrix.det_one
  intro h; rw [h, zero_mul] at h_det_prod; exact one_ne_zero h_det_prod.symm

/-- Unfold `blockEmbedGL` to its underlying matrix. -/
private lemma blockEmbedGL_val_eq {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    (blockEmbedGL X).val = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm) := rfl

/-- `blockEmbedGL` is multiplicative. -/
private lemma blockEmbedGL_mul {k : ℕ} (X Y : GL (Fin (k + 1)) ℚ) :
    blockEmbedGL (X * Y) = blockEmbedGL X * blockEmbedGL Y := by
  apply Units.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  have lhs : (blockEmbedGL (X * Y)).val =
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 (X.val * Y.val)).submatrix e e := by
    rw [blockEmbedGL_val_eq, Units.val_mul]
  have rhs : (blockEmbedGL X * blockEmbedGL Y).val =
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix e e *
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 Y.val).submatrix e e := by
    rw [Units.val_mul, blockEmbedGL_val_eq, blockEmbedGL_val_eq]
  rw [lhs, rhs,
    show Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 (X.val * Y.val) =
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val *
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 Y.val from by
      rw [Matrix.fromBlocks_multiply]; simp]
  exact (Matrix.submatrix_mul_equiv _ _ e e e).symm

/-- `blockEmbedGL` sends `1` to `1`. -/
private lemma blockEmbedGL_one {k : ℕ} :
    blockEmbedGL (1 : GL (Fin (k + 1)) ℚ) = 1 := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  show (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0
        ((1 : GL (Fin (k + 1)) ℚ).val)).submatrix e e = (1 : GL (Fin (k + 2)) ℚ).val
  rw [show ((1 : GL (Fin (k + 1)) ℚ).val) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) from rfl,
      Matrix.fromBlocks_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

/-- `blockEmbedGL` preserves inverses. -/
private lemma blockEmbedGL_inv {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    blockEmbedGL X⁻¹ = (blockEmbedGL X)⁻¹ := by
  apply mul_left_cancel (a := blockEmbedGL X)
  rw [mul_inv_cancel, ← blockEmbedGL_mul, mul_inv_cancel, blockEmbedGL_one]

/-- `blockEmbedGL (diagMat (k+1) a) = diagMat (k+2) (Fin.cons 1 a)`: the block
embedding of a diagonal matrix is the `cons 1`-prepended diagonal matrix. -/
private lemma blockEmbedGL_diagMat {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    blockEmbedGL (diagMat (k + 1) a) = diagMat (k + 2) (Fin.cons 1 a) := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  rw [diagMat_val _ _ ha, diagMat_val _ _ (cons_one_pos ha)]
  ext i j
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j <;>
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.fromBlocks,
          Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
          Fin.subNat, Fin.succ_inj, Fin.cons_succ,
          (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]

/-- For `ν : SL_{k+1}(ℤ)`, `blockEmbedGL (mapGL ν) = mapGL (slSuccEmbed ν)`: the GL
block embedding agrees with `slSuccEmbed` at the SL level after `mapGL`-casting. -/
private lemma blockEmbedGL_mapGL_eq {k : ℕ} (ν : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    blockEmbedGL (mapGL ℚ ν) = mapGL ℚ (slSuccEmbed ν) := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  ext i j
  simp only [Matrix.submatrix_apply, mapGL_coe_matrix, algebraMap_int_eq,
             SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  · rw [slSuccEmbed_val_zero_zero]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_zero_succ]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_succ_zero]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_succ_succ]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply, Fin.subNat]

/-- On the Hecke subgroup `H_{k+1}`, `blockEmbedGL` agrees with `slSuccEmbed_H`
(viewed as GL elements). Both unfold to `fromBlocks 1 0 0 σ_mat` (up to submatrix
reindexing) where `σ_mat` is the rational-valued matrix of the H element. The proof
goes through the SL-level `blockEmbedGL_mapGL_eq` after writing `σ = mapGL ℚ (toSL σ)`. -/
private lemma blockEmbedGL_slSuccEmbed_H_eq {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    blockEmbedGL (σ : GL (Fin (k + 1)) ℚ) = (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) := by
  rw [show (σ : GL (Fin (k + 1)) ℚ) = mapGL ℚ (toSL σ) from (toSL_spec σ).symm,
    blockEmbedGL_mapGL_eq, slSuccEmbed_H_val]

/-! ### Block-form predecessor `slPredEmbed`

Partial inverse to `slSuccEmbed`: given `M ∈ SL_{k+2}(ℤ)` satisfying block-form
hypotheses (`M 0 0 = 1` and `M i.succ 0 = 0` for every `i`), extract the
`(k+1) × (k+1)` bottom-right submatrix as an `SL_{k+1}(ℤ)` element.

- `slPredEmbed M h_diag h_col : SpecialLinearGroup (Fin (k+1)) ℤ` — the
  predecessor, with `det = 1` by Laplace expansion along column 0.
- `slPredEmbed_slSuccEmbed_eq`: retraction `slPredEmbed ∘ slSuccEmbed = id`.
- `slSuccEmbed_slPredEmbed_eq`: section `slSuccEmbed ∘ slPredEmbed = id` on
  block-form matrices (also requires first row off `(0,0)` to be zero). -/

/-- **Block-form predecessor.** Takes `M ∈ SL_{k+2}(ℤ)` with `M 0 0 = 1` and
`M i.succ 0 = 0` for every `i`; returns the bottom-right `(k+1) × (k+1)`
submatrix, viewed as an `SL_{k+1}(ℤ)` element. The `det = 1` property follows
from Laplace expansion along column 0 (only one non-zero term). -/
private noncomputable def slPredEmbed {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0) :
    SpecialLinearGroup (Fin (k + 1)) ℤ :=
  ⟨M.1.submatrix Fin.succ Fin.succ, by
    have h_det_M : M.1.det = 1 := M.2
    have h_laplace := Matrix.det_succ_column_zero M.1
    rw [Fin.sum_univ_succ] at h_laplace
    simp only [Fin.val_zero, pow_zero, h_diag, one_mul, Fin.succAbove_zero] at h_laplace
    have h_tail : (∑ i : Fin (k + 1),
        (-1 : ℤ) ^ ((i.succ : Fin (k + 2)) : ℕ) * M.1 i.succ 0 *
          (M.1.submatrix (i.succ).succAbove Fin.succ).det) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [h_col i]; ring
    rw [h_tail, add_zero] at h_laplace
    rw [h_det_M] at h_laplace
    exact h_laplace.symm⟩

/-- Unfolding the underlying matrix of `slPredEmbed`. -/
private lemma slPredEmbed_val_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0) :
    (slPredEmbed M h_diag h_col).1 = M.1.submatrix Fin.succ Fin.succ := rfl

/-- Entry-level unfolding: `(slPredEmbed M).1 i j = M.1 i.succ j.succ`. -/
private lemma slPredEmbed_val_apply {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0)
    (i j : Fin (k + 1)) :
    (slPredEmbed M h_diag h_col).1 i j = M.1 i.succ j.succ := rfl

/-- **Retraction.** `slPredEmbed (slSuccEmbed M) _ _ = M`. The block-form
hypotheses are automatically satisfied by `slSuccEmbed M`, witnessed by
`slSuccEmbed_val_zero_zero` and `slSuccEmbed_val_succ_zero`. -/
private lemma slPredEmbed_slSuccEmbed_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slPredEmbed (slSuccEmbed M) (slSuccEmbed_val_zero_zero M)
      (fun i ↦ slSuccEmbed_val_succ_zero M i) = M := by
  apply Subtype.ext
  ext i j
  rw [slPredEmbed_val_apply]
  exact slSuccEmbed_val_succ_succ M i j

/-- **Section.** `slSuccEmbed (slPredEmbed M _ _) = M` for `M` satisfying the
full block-form condition (first column and first row zero off the `(0, 0)`
entry). -/
private lemma slSuccEmbed_slPredEmbed_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), M.1 0 j.succ = 0) :
    slSuccEmbed (slPredEmbed M h_diag h_col) = M := by
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  · rw [slSuccEmbed_val_zero_zero, h_diag]
  · rw [slSuccEmbed_val_zero_succ, h_row j']
  · rw [slSuccEmbed_val_succ_zero, h_col i']
  · rw [slSuccEmbed_val_succ_succ]; rfl

/-- **H-level predecessor.** Given `σ ∈ H_{k+2}` whose underlying `SL_{k+2}(ℤ)`
matrix satisfies the block-form hypotheses, extract `σ_m ∈ H_{k+1}`. Built by
applying `slPredEmbed` at the SL level after `toSL`. -/
private noncomputable def slPredEmbed_H {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0) :
    (GL_pair (k + 1)).H := by
  refine ⟨mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col), ?_⟩
  show (mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col) : GL (Fin (k + 1)) ℚ) ∈
    SLnZ_subgroup (k + 1)
  exact ⟨slPredEmbed (toSL σ) h_diag h_col, rfl⟩

/-- Unfold `slPredEmbed_H σ` to its GL-level value. -/
private lemma slPredEmbed_H_val {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0) :
    (slPredEmbed_H σ h_diag h_col : GL (Fin (k + 1)) ℚ) =
      mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col) := rfl

/-- **Section at the H level.** When `σ ∈ H_{k+2}` satisfies the full block-form
hypotheses, `slSuccEmbed_H (slPredEmbed_H σ) = σ` (at the H subtype level). -/
private lemma slSuccEmbed_H_slPredEmbed_H_eq {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), (toSL σ).1 0 j.succ = 0) :
    slSuccEmbed_H (slPredEmbed_H σ h_diag h_col) = σ := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL (slPredEmbed_H σ h_diag h_col))) :
      GL (Fin (k + 2)) ℚ) = (σ : GL (Fin (k + 2)) ℚ)
  have h_toSL_eq : toSL (slPredEmbed_H σ h_diag h_col) =
      slPredEmbed (toSL σ) h_diag h_col := by
    apply mapGL_injective (k + 1)
    rw [toSL_spec (slPredEmbed_H σ h_diag h_col), slPredEmbed_H_val]
  rw [h_toSL_eq, slSuccEmbed_slPredEmbed_eq _ h_diag h_col h_row]
  exact toSL_spec σ

/-- **Stabilizer preservation for the predecessor.** If `σ ∈ H_{k+2}` satisfies
the full block-form hypotheses and lies in the stabilizer of `diag(Fin.cons 1 a)`
at dim `k+2`, then `slPredEmbed_H σ` lies in the stabilizer of `diag a` at
dim `k+1`. Proved by converting `σ` to `slSuccEmbed_H (slPredEmbed_H σ)` via the
section and invoking `slSuccEmbed_H_stab_diagMat_converse`. -/
private lemma slPredEmbed_H_stab_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), (toSL σ).1 0 j.succ = 0)
    (hσ : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 1) a)⁻¹ *
        (slPredEmbed_H σ h_diag h_col : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a ∈ (GL_pair (k + 1)).H := by
  have h_eq : (σ : GL (Fin (k + 2)) ℚ) =
      (slSuccEmbed_H (slPredEmbed_H σ h_diag h_col) : GL (Fin (k + 2)) ℚ) := by
    rw [slSuccEmbed_H_slPredEmbed_H_eq σ h_diag h_col h_row]
  rw [h_eq] at hσ
  exact slSuccEmbed_H_stab_diagMat_converse a ha (slPredEmbed_H σ h_diag h_col) hσ

/-- **`blockEmbedGL` is injective.** If the block embeddings of two GL elements
agree at dim `k+2`, the original elements agree at dim `k+1`. Follows from
entry-by-entry matrix equality at the bottom-right block. -/
private lemma blockEmbedGL_injective {k : ℕ} :
    Function.Injective (blockEmbedGL : GL (Fin (k + 1)) ℚ → GL (Fin (k + 2)) ℚ) := by
  intro X Y h
  apply Units.ext
  ext i j
  have h_val : (blockEmbedGL X).val i.succ j.succ = (blockEmbedGL Y).val i.succ j.succ :=
    congr_arg (fun (u : GL (Fin (k + 2)) ℚ) ↦ u.val i.succ j.succ) h
  have h_X_unfold : (blockEmbedGL X).val i.succ j.succ = X.val i j := by
    rw [blockEmbedGL_val_eq]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
          Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat]
  have h_Y_unfold : (blockEmbedGL Y).val i.succ j.succ = Y.val i j := by
    rw [blockEmbedGL_val_eq]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
          Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat]
  rw [h_X_unfold, h_Y_unfold] at h_val
  exact h_val

/-- **Membership descent through `blockEmbedGL`.** If the block embedding of `h`
lies in `(GL_pair (k+2)).H = SLnZ_subgroup (k+2)`, then `h` itself lies in
`SLnZ_subgroup (k+1)`. Proved by extracting the bottom-right block of the `SL`
witness at dim `k+2` via `slPredEmbed`. -/
private lemma blockEmbedGL_mem_H_imp {k : ℕ} (h : GL (Fin (k + 1)) ℚ)
    (hh : blockEmbedGL h ∈ (GL_pair (k + 2)).H) :
    h ∈ (GL_pair (k + 1)).H := by
  obtain ⟨ν, hν⟩ := hh
  have hν_val : ∀ p q : Fin (k + 2),
      ((ν.1 p q : ℤ) : ℚ) = (blockEmbedGL h).val p q := by
    intro p q
    have := congr_arg (fun (u : GL (Fin (k + 2)) ℚ) ↦ u.val p q) hν
    simpa [mapGL_coe_matrix, algebraMap_int_eq, Matrix.map_apply] using this
  have h_ν_diag : ν.1 0 0 = 1 := by
    have h0 := hν_val 0 0
    rw [blockEmbedGL_val_eq] at h0
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases] at h0
    exact_mod_cast h0
  have h_ν_col : ∀ i : Fin (k + 1), ν.1 i.succ 0 = 0 := by
    intro i
    have hi := hν_val i.succ 0
    rw [blockEmbedGL_val_eq] at hi
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat] at hi
    exact_mod_cast hi
  have h_ν_row : ∀ j : Fin (k + 1), ν.1 0 j.succ = 0 := by
    intro j
    have hj := hν_val 0 j.succ
    rw [blockEmbedGL_val_eq] at hj
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat] at hj
    exact_mod_cast hj
  set ν_m := slPredEmbed ν h_ν_diag h_ν_col with hν_m_def
  refine ⟨ν_m, ?_⟩
  apply blockEmbedGL_injective
  have h_section : slSuccEmbed ν_m = ν :=
    slSuccEmbed_slPredEmbed_eq ν h_ν_diag h_ν_col h_ν_row
  rw [blockEmbedGL_mapGL_eq, h_section, hν]

/-- **Block-form fiber descent.** Given `σ_m, τ_m ∈ H_{k+1}`, if the lifted
H-membership condition at dim `k+2` (with `Fin.cons 1 _` diagonals) holds for
the `slSuccEmbed_H` images, then the corresponding dim-`k+1` H-membership
condition holds for `σ_m, τ_m`. This is the "reverse fiber transfer" — converse
of `slSuccEmbed_H_fiber_transfer`. Proved by rewriting both sides as
`blockEmbedGL`-images and invoking `blockEmbedGL_mem_H_imp`. -/
private lemma slSuccEmbed_H_fiber_transfer_converse {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (σ_m τ_m : (GL_pair (k + 1)).H)
    (h : (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
         (slSuccEmbed_H σ_m : GL (Fin (k + 2)) ℚ) *
         diagMat (k + 2) (Fin.cons 1 a) *
         (slSuccEmbed_H τ_m : GL (Fin (k + 2)) ℚ) *
         diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 1) c)⁻¹ * (σ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a *
      (τ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  have h_eq : (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
      (slSuccEmbed_H σ_m : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) *
      (slSuccEmbed_H τ_m : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) =
    blockEmbedGL ((diagMat (k + 1) c)⁻¹ * (σ_m : GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) a * (τ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b) := by
    rw [blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul,
      blockEmbedGL_inv, blockEmbedGL_diagMat _ hc, blockEmbedGL_diagMat _ ha,
      blockEmbedGL_diagMat _ hb, ← blockEmbedGL_slSuccEmbed_H_eq σ_m,
      ← blockEmbedGL_slSuccEmbed_H_eq τ_m]
  rw [h_eq] at h
  exact blockEmbedGL_mem_H_imp _ h

/-- **Fiber-condition block transfer** (the five-factor key lemma for the ≥
direction). If the dim-`k+1` "conjugation-like" expression
`(diagMat c)⁻¹ · σ · diagMat a · τ · diagMat b` lies in `H_{k+1}`, then the
analogous dim-`k+2` expression with `Fin.cons 1` diagonals and `slSuccEmbed_H`
lifts of `σ, τ` lies in `H_{k+2}`. This is the core fiber-transfer for the
block-embedding injection.

Proof strategy: apply `blockEmbedGL` to both sides of the dim-`k+1` equation and
use `blockEmbedGL_mul/_inv/_diagMat/_slSuccEmbed_H_eq/_mapGL_eq` to rewrite each
factor into its dim-`k+2` counterpart. -/
private lemma slSuccEmbed_H_fiber_transfer {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (σ τ : (GL_pair (k + 1)).H)
    (h : (diagMat (k + 1) c)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a *
         (τ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈ (GL_pair (k + 1)).H) :
    (diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) * (slSuccEmbed_H τ : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨slSuccEmbed ν, ?_⟩
  have h_img := congr_arg (blockEmbedGL (k := k)) hν
  rw [blockEmbedGL_mapGL_eq] at h_img
  rw [blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul,
      blockEmbedGL_inv, blockEmbedGL_diagMat _ hc, blockEmbedGL_diagMat _ ha,
      blockEmbedGL_diagMat _ hb, blockEmbedGL_slSuccEmbed_H_eq σ,
      blockEmbedGL_slSuccEmbed_H_eq τ] at h_img
  exact h_img

/-- **Right-coset / H-membership pivot for the diagMat fiber.** The fiber-pair
right-coset condition `{i.out · diagMat a} · {j.out · diagMat b} · H = {diagMat c} · H`
is logically equivalent to the H-membership condition fed to
`slSuccEmbed_H_fiber_transfer`. This makes the block-embedding fiber transfer
applicable directly to fiber-counting arguments at the diagMat-delta level. -/
private lemma fiber_diagMat_iff_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (_ : ∀ i, 0 < a i) (_ : ∀ i, 0 < b i) (_ : ∀ i, 0 < c i)
    (σ τ : (GL_pair n).H) :
    (({(σ : GL (Fin n) ℚ) * diagMat n a} : Set _) *
        {(τ : GL (Fin n) ℚ) * diagMat n b} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(diagMat n c : GL (Fin n) ℚ)} * ((GL_pair n).H : Set (GL (Fin n) ℚ))) ↔
    (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
        (τ : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H := by
  rw [Set.singleton_mul_singleton]
  constructor
  · intro h_eq
    have hmem : (σ : GL (Fin n) ℚ) * diagMat n a *
        ((τ : GL (Fin n) ℚ) * diagMat n b) ∈
        ({(diagMat n c : GL (Fin n) ℚ)} : Set _) *
          ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
      rw [← h_eq]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
    obtain ⟨_, hd_eq, h, hh, hprod⟩ := hmem
    rw [Set.mem_singleton_iff] at hd_eq
    subst hd_eq
    simp only at hprod
    have h_eq_factor : (diagMat n c)⁻¹ *
        ((σ : GL (Fin n) ℚ) * diagMat n a *
          ((τ : GL (Fin n) ℚ) * diagMat n b)) = h := by
      rw [← hprod]; group
    rw [show (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
          (τ : GL (Fin n) ℚ) * diagMat n b =
        (diagMat n c)⁻¹ * ((σ : GL (Fin n) ℚ) * diagMat n a *
          ((τ : GL (Fin n) ℚ) * diagMat n b)) by group, h_eq_factor]
    exact hh
  · intro h_mem
    set h_elt := (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
        (τ : GL (Fin n) ℚ) * diagMat n b
    ext y
    constructor
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt * k, (GL_pair n).H.mul_mem h_mem hk, ?_⟩
      simp only [h_elt]; group
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt⁻¹ * k, (GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem h_mem) hk, ?_⟩
      simp only [h_elt]; group

/-- `decompQuot` is invariant under changing the Δ-element when the underlying GL-values agree.
This gives an `Equiv` via `Subgroup.quotientEquivOfEq` (the stabilizer depends only on the
GL-value, not on the Δ-membership proof). -/
noncomputable def decompQuot_val_equiv {n : ℕ} [NeZero n]
    (g₁ g₂ : (GL_pair n).Δ) (h : (g₁ : GL (Fin n) ℚ) = g₂) :
    decompQuot (GL_pair n) g₁ ≃ decompQuot (GL_pair n) g₂ :=
  Equiv.cast (congrArg _ (Subtype.ext h))

/-- Strip H-factors from `rep(T_diag a)` to get `decompQuot(rep) ≃ decompQuot(diagMat_delta)`. -/
noncomputable def decompQuot_rep_to_diagMat {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ≃
    decompQuot (GL_pair n) (diagMat_delta n a) := by
  let L_data := Classical.indefiniteDescription _ (T_diag_rep_decompose a ha)
  let L : (GL_pair n).H := ⟨L_data.val, L_data.prop.1⟩
  let R_data := Classical.indefiniteDescription _ L_data.prop.2
  let R : (GL_pair n).H := ⟨R_data.val, R_data.prop.1⟩
  have hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
    ↑L * diagMat n a * ↑R := R_data.prop.2
  have hmem : (↑L * diagMat n a * ↑R : GL (Fin n) ℚ) ∈ (GL_pair n).Δ :=
    hLR ▸ (T_diag a).rep.2
  have hD_eq : diagMat_delta n a =
      ⟨diagMat n a, diagMat_mem_posDetInt n a ha⟩ :=
    Subtype.ext (diagMat_delta_val n a ha)
  exact (decompQuot_val_equiv _ ⟨_, hmem⟩ hLR).trans
    (hD_eq ▸ decompQuot_double_H_equiv (GL_pair n)
      ⟨diagMat n a, diagMat_mem_posDetInt n a ha⟩ L R hmem)

/-! ### Lattice model for heckeMultiplicity (Shimura Propositions 3.14-3.15)

A Z-lattice in `ℚ^n` is a free Z-submodule of rank `n` that spans `ℚ^n`.
For `L = ℤ^n` (standard lattice) and `α = diag(d₁,...,dₙ)`, the lattice `Lα = α·ℤ^n`
has elementary divisors `{L:Lα} = {d₁,...,dₙ}`.

Shimura's Proposition 3.15 expresses the Hecke multiplication coefficient `μ(α, β, ξ)` as
the number of intermediate lattices `M` with `N ⊂ M ⊂ L` and specific elementary divisors.

For the block embedding (Shimura Lemma 3.19): when all three diagonals have first entry 1,
every intermediate lattice `M'` at dimension `m+1` decomposes as `M' = ℤu₀ + M`, giving
a bijection with `m`-dimensional intermediate lattices. -/

/-- A Z-lattice in `ℚ^n` is represented as `σ · diagMat(d) · ℤ^n` for `σ ∈ SL_n(ℤ)`.
Two elements `(σ₁, d)` and `(σ₂, d)` give the same lattice iff `σ₁ ~ σ₂` in `decompQuot`.
This is Shimura's lattice model (§3.2). -/
private def IntLattice (n : ℕ) [NeZero n] (d : Fin n → ℕ) (_ : ∀ i, 0 < d i) :=
  decompQuot (GL_pair n) (diagMat_delta n d)


/-! ### Compensated rep-shift helpers for the diagMat-level ≥ direction

Local analogues of the private `Associativity.lean` helpers, plus a `q = 1`
specialization of `coset_shift_fwd` and a left-multiplication cancellation
lemma. These are needed for the compensated injection used in
`heckeMultiplicity_block_embed_ge_diagMat`. -/

/-- `g⁻¹ · n⁻¹ · g ∈ H` whenever `n` lives in the conjugate stabilizer of `g`. -/
private lemma conjAct_inv_mem_of_subgroupOf {n : ℕ} [NeZero n] (g : GL (Fin n) ℚ)
    (m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H) :
    g⁻¹ * (m : GL (Fin n) ℚ)⁻¹ * g ∈ (GL_pair n).H := by
  have hm := m.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hm
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hm
  have := (GL_pair n).H.inv_mem hm; convert this using 1; group

/-- `g⁻¹ · n · g ∈ H` whenever `n` lives in the conjugate stabilizer of `g`. -/
private lemma conjAct_mem_of_subgroupOf {n : ℕ} [NeZero n] (g : GL (Fin n) ℚ)
    (m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H) :
    g⁻¹ * (m : GL (Fin n) ℚ) * g ∈ (GL_pair n).H := by
  have hm := m.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hm
  simpa [ConjAct.ofConjAct_toConjAct] using hm

/-- Lift the `H`-level relation `(⟦h⟧).out = h · n` from `QuotientGroup.mk_out_eq_mul`
to the underlying `GL ℚ` element. -/
private lemma mk_out_coe_eq_mul {n : ℕ} [NeZero n] {g : GL (Fin n) ℚ} {h : (GL_pair n).H}
    {m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H}
    (hn_eq : (⟦h⟧ : (GL_pair n).H ⧸
        (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H).out = h * m) :
    (((⟦h⟧ : (GL_pair n).H ⧸
        (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H).out : (GL_pair n).H) :
      GL (Fin n) ℚ) = (h : GL (Fin n) ℚ) * (m : GL (Fin n) ℚ) := by
  have := congr_arg (Subtype.val : ↥(GL_pair n).H → GL (Fin n) ℚ) hn_eq
  simpa [Subgroup.coe_mul] using this

/-- `q = 1` specialization of `Associativity.coset_shift_fwd`: shift the underlying
representatives `(a, b) ↦ (a · n₁, gA⁻¹ · n₁⁻¹ · gA · b · n₂)` while keeping the
target right-coset `{gC} · H` fixed. -/
private lemma coset_shift_fwd_q1 {n : ℕ} [NeZero n]
    (a b a' b' gA gB gC n₁ n₂ : GL (Fin n) ℚ)
    (hcond : ({a * gA * (b * gB)} : Set _) * ((GL_pair n).H : Set _) =
      {gC} * ((GL_pair n).H : Set _))
    (ha' : a' = a * n₁)
    (hb' : b' = gA⁻¹ * n₁⁻¹ * gA * b * n₂)
    (hn₂_conj : gB⁻¹ * n₂ * gB ∈ (GL_pair n).H) :
    ({a' * gA * (b' * gB)} : Set _) * ((GL_pair n).H : Set _) =
      {gC} * ((GL_pair n).H : Set _) := by
  subst ha' hb'
  apply leftCoset_eq_of_not_disjoint
  rw [Set.not_disjoint_iff]
  refine ⟨a * n₁ * gA * (gA⁻¹ * n₁⁻¹ * gA * b * n₂ * gB),
    ⟨1, (GL_pair n).H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a * gA * (b * gB) ∈ ({gC} : Set _) * ((GL_pair n).H : Set _) := by
    rw [← hcond]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by group⟩
  obtain ⟨y, h_eq, h₀, hh₀, hprod⟩ := hmem
  rw [Set.mem_singleton_iff] at h_eq
  rw [h_eq] at hprod
  refine ⟨h₀ * (gB⁻¹ * n₂ * gB), (GL_pair n).H.mul_mem hh₀ hn₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc a * n₁ * gA * (gA⁻¹ * n₁⁻¹ * gA * b * n₂ * gB)
      = (a * gA * (b * gB)) * (gB⁻¹ * n₂ * gB) := by group
    _ = gC * (h₀ * (gB⁻¹ * n₂ * gB)) := by
        simp only at hprod
        rw [← hprod]; group

/-- Left-multiplication cancellation in `decompQuot`: equality of `⟦h * x⟧` and
`⟦h * y⟧` reduces to equality of `⟦x⟧` and `⟦y⟧`, since
`(h * x)⁻¹ * (h * y) = x⁻¹ * y`. -/
private lemma decompQuot_left_mul_cancel {n : ℕ} [NeZero n]
    (g : (GL_pair n).Δ) (h x y : (GL_pair n).H)
    (heq : (⟦h * x⟧ : decompQuot (GL_pair n) g) = ⟦h * y⟧) :
    (⟦x⟧ : decompQuot (GL_pair n) g) = ⟦y⟧ := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply] at heq ⊢
  convert heq using 1
  rw [show (h * x)⁻¹ * (h * y) = x⁻¹ * y by group]

/-- Narrowly typed `Quotient.out_eq` for `decompQuot`: avoids the motive-correctness
trap that `rw [← Quotient.out_eq …]` falls into because `decompQuot` is mentioned
explicitly in the type. -/
private lemma decompQuot_out_eq {n : ℕ} [NeZero n] {g : (GL_pair n).Δ}
    (q : decompQuot (GL_pair n) g) :
    (⟦q.out⟧ : decompQuot (GL_pair n) g) = q := Quotient.out_eq q

set_option maxHeartbeats 1200000 in
/-- **Diagonal-level ≥ direction of `heckeMultiplicity_block_embed`.** Compensated
injection via `coset_shift_fwd_q1`. -/
private lemma heckeMultiplicity_block_embed_ge_diagMat {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have h_dval_a : ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 a) hcons_a
  have h_dval_b : ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 b) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 b) hcons_b
  have h_dval_c : ((diagMat_delta (k + 2) (Fin.cons 1 c) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 c) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 c) hcons_c
  have h_dval_a1 : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b1 : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c1 : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  let getN₁ : (GL_pair (k + 2)).H →
      (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf (GL_pair (k + 2)).H :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose
  have hgetN₁_spec : ∀ σ : (GL_pair (k + 2)).H,
      (⟦σ⟧ : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))).out =
      σ * getN₁ σ :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose_spec
  let mkYbase : (GL_pair (k + 2)).H → (GL_pair (k + 2)).H → (GL_pair (k + 2)).H :=
    fun σ τ ↦ ⟨_, conjAct_inv_mem_of_subgroupOf
      ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ)
      (getN₁ σ)⟩ * τ
  let SrcType : Type := {p : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) ×
            decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b) |
            ({(p.1.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
            ((GL_pair (k + 1)).H : Set _) =
            {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
              ((GL_pair (k + 1)).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) ×
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)) |
            ({(p.1.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦slSuccEmbed_H i.out⟧,
      ⟦mkYbase (slSuccEmbed_H i.out) (slSuccEmbed_H j.out)⟧),
      by
        have h_iff := fiber_diagMat_iff_mem_H a b c ha hb hc i.out j.out
        rw [← h_dval_a1, ← h_dval_b1, ← h_dval_c1] at h_iff
        have h_mem_pre := h_iff.mp hcond
        have h_mem : (diagMat (k + 1) c)⁻¹ * (i.out : GL (Fin (k + 1)) ℚ) *
            diagMat (k + 1) a * (j.out : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈
              (GL_pair (k + 1)).H := by
          convert h_mem_pre using 2 <;> simp [h_dval_a1, h_dval_b1, h_dval_c1]
        have h_mem' := slSuccEmbed_H_fiber_transfer a b c ha hb hc i.out j.out h_mem
        have h_iff_lift := fiber_diagMat_iff_mem_H (Fin.cons 1 a) (Fin.cons 1 b)
          (Fin.cons 1 c) hcons_a hcons_b hcons_c
          (slSuccEmbed_H i.out) (slSuccEmbed_H j.out)
        have h_rc_lift := h_iff_lift.mpr h_mem'
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_rc_lift
        set n₁ := getN₁ (slSuccEmbed_H i.out) with hn₁_def
        set Yval := mkYbase (slSuccEmbed_H i.out) (slSuccEmbed_H j.out) with hY_def
        have hi₂_out_eq :
            ((⟦slSuccEmbed_H i.out⟧ : decompQuot (GL_pair (k + 2))
              (diagMat_delta (k + 2) (Fin.cons 1 a))).out : GL (Fin (k + 2)) ℚ) =
            (slSuccEmbed_H i.out : GL (Fin (k + 2)) ℚ) *
              (n₁ : GL (Fin (k + 2)) ℚ) := by
          have h := hgetN₁_spec (slSuccEmbed_H i.out)
          have := congr_arg (Subtype.val : ↥(GL_pair (k + 2)).H → GL (Fin (k + 2)) ℚ) h
          simpa [Subgroup.coe_mul] using this
        obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 b) :
              (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) •
            (GL_pair (k + 2)).H).subgroupOf (GL_pair (k + 2)).H) Yval
        have hj₂_out_eq : ((⟦Yval⟧ : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 b))).out :
            GL (Fin (k + 2)) ℚ) = (Yval : GL (Fin (k + 2)) ℚ) *
              (n₂ : GL (Fin (k + 2)) ℚ) := by
          have := congr_arg (Subtype.val :
            ↥(GL_pair (k + 2)).H → GL (Fin (k + 2)) ℚ) hn₂_eq
          simpa [Subgroup.coe_mul] using this
        have hYval_coe : (Yval : GL (Fin (k + 2)) ℚ) =
            ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ)⁻¹ * (n₁ : GL (Fin (k + 2)) ℚ)⁻¹ *
            ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ) *
            (slSuccEmbed_H j.out : GL (Fin (k + 2)) ℚ) := by
          show ((mkYbase (slSuccEmbed_H i.out) (slSuccEmbed_H j.out) :
            (GL_pair (k + 2)).H) : GL (Fin (k + 2)) ℚ) = _
          simp [mkYbase, Subgroup.coe_mul, hn₁_def]
        have hj₂_form : ((⟦Yval⟧ : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 b))).out : GL (Fin (k + 2)) ℚ) =
            ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ)⁻¹ * (n₁ : GL (Fin (k + 2)) ℚ)⁻¹ *
            ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ) *
            (slSuccEmbed_H j.out : GL (Fin (k + 2)) ℚ) *
            (n₂ : GL (Fin (k + 2)) ℚ) := by
          rw [hj₂_out_eq, hYval_coe]
        have hn₂_conj :
            ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ)⁻¹ * (n₂ : GL (Fin (k + 2)) ℚ) *
            ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ) ∈ (GL_pair (k + 2)).H :=
          conjAct_mem_of_subgroupOf _ n₂
        have h_rc_lift_merged :
            ({(slSuccEmbed_H i.out : GL (Fin (k + 2)) ℚ) *
                ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
                  GL (Fin (k + 2)) ℚ) *
                ((slSuccEmbed_H j.out : GL (Fin (k + 2)) ℚ) *
                  ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
                    GL (Fin (k + 2)) ℚ))} : Set _) *
            ((GL_pair (k + 2)).H : Set _) =
            {((diagMat_delta (k + 2) (Fin.cons 1 c) : (GL_pair (k + 2)).Δ) :
              GL (Fin (k + 2)) ℚ)} * ((GL_pair (k + 2)).H : Set _) := by
          rw [← Set.singleton_mul_singleton]; exact h_rc_lift
        have h_target := coset_shift_fwd_q1
          (slSuccEmbed_H i.out : GL (Fin (k + 2)) ℚ)
          (slSuccEmbed_H j.out : GL (Fin (k + 2)) ℚ)
          ((⟦slSuccEmbed_H i.out⟧ : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 a))).out : GL (Fin (k + 2)) ℚ)
          ((⟦Yval⟧ : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 b))).out : GL (Fin (k + 2)) ℚ)
          ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
            GL (Fin (k + 2)) ℚ)
          ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
            GL (Fin (k + 2)) ℚ)
          ((diagMat_delta (k + 2) (Fin.cons 1 c) : (GL_pair (k + 2)).Δ) :
            GL (Fin (k + 2)) ℚ)
          (n₁ : GL (Fin (k + 2)) ℚ) (n₂ : GL (Fin (k + 2)) ℚ)
          h_rc_lift_merged hi₂_out_eq hj₂_form hn₂_conj
        rw [← Set.singleton_mul_singleton] at h_target
        exact h_target⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦slSuccEmbed_H i₁.out⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) =
      ⟦slSuccEmbed_H i₂.out⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦mkYbase (slSuccEmbed_H i₁.out) (slSuccEmbed_H j₁.out)⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
      ⟦mkYbase (slSuccEmbed_H i₂.out) (slSuccEmbed_H j₂.out)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ := by
    calc i₁
        = (⟦i₁.out⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) :=
          (decompQuot_out_eq i₁).symm
      _ = ⟦i₂.out⟧ := by
          apply decompQuot_slSuccEmbed_diagMat_injective a ha
          show (⟦slSuccEmbed_H i₁.out⟧ :
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) =
            ⟦slSuccEmbed_H i₂.out⟧
          exact h_i_eq
      _ = i₂ := decompQuot_out_eq i₂
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (diagMat_delta (k + 2) (Fin.cons 1 b))
    ⟨_, conjAct_inv_mem_of_subgroupOf
      ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ)
      (getN₁ (slSuccEmbed_H i₁.out))⟩
    (slSuccEmbed_H j₁.out) (slSuccEmbed_H j₂.out) h_j_eq
  have h_j_final : j₁ = j₂ := by
    calc j₁
        = (⟦j₁.out⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) :=
          (decompQuot_out_eq j₁).symm
      _ = ⟦j₂.out⟧ := by
          apply decompQuot_slSuccEmbed_diagMat_injective b hb
          show (⟦slSuccEmbed_H j₁.out⟧ :
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
            ⟦slSuccEmbed_H j₂.out⟧
          exact h_j_cancel
      _ = j₂ := decompQuot_out_eq j₂
  subst h_j_final
  rfl

/-! ### Rep-to-diagMat bridge (Shimura Prop 3.4, diagonal level)

The Hecke multiplicity at `HeckeCoset.rep (T_diag …)` equals the multiplicity at
`diagMat_delta …`. Proof: using `rep(T_diag x) = L_x · D_x · R_x` with
`L_x, R_x ∈ H`, construct a `Quotient.map'` between the fiber-subtype counts,
with asymmetric transport `⟦σ⟧_{rep T(a)} ↦ ⟦L_c⁻¹ · σ · L_a⟧_{D(a)}` on the
first component and `⟦τ⟧_{rep T(b)} ↦ ⟦R_a · τ · L_b⟧_{D(b)}` on the second.
The well-definedness of these maps holds because the H-conjugation bridging the
rep-level and diag-level stabilizers is absorbed by the asymmetric shift. -/

/-- Bridging iff between rep-level and diag-level stabilizer membership: for
`σ ∈ H`, `σ ∈ Stab(rep T(a))` iff `La⁻¹ · σ · La ∈ Stab(D_a)`.
Proof uses H-conjugation by `Ra` to strip the outer Ra factors after substituting
`rep T(a) = La · D_a · Ra`. -/
private lemma rep_stab_iff_diag_stab {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (_ : ∀ i, 0 < a i)
    (La Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ : (GL_pair n).H) :
    σ ∈ (ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H ↔
    (⟨(La : GL (Fin n) ℚ)⁻¹ * σ * (La : GL (Fin n) ℚ),
        (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem La.2) σ.2)
          La.2⟩ : (GL_pair n).H) ∈
      (ConjAct.toConjAct (diagMat n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H := by
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [hLR]
  constructor
  · intro hmem
    have h1 : (Ra : GL (Fin n) ℚ) *
        (((La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))⁻¹ *
          (σ : GL (Fin n) ℚ) *
          ((La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))) *
        (Ra : GL (Fin n) ℚ)⁻¹ ∈ (GL_pair n).H :=
      (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem Ra.2 hmem) ((GL_pair n).H.inv_mem Ra.2)
    convert h1 using 1; group
  · intro hmem
    have h1 : (Ra : GL (Fin n) ℚ)⁻¹ *
        ((diagMat n a)⁻¹ * ((La : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
          (La : GL (Fin n) ℚ)) * diagMat n a) *
        (Ra : GL (Fin n) ℚ) ∈ (GL_pair n).H :=
      (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Ra.2) hmem) Ra.2
    convert h1 using 1; group

/-- Bridging iff for the second component: for `τ ∈ H`,
`τ ∈ Stab(rep T(b))` iff `Lb⁻¹ · τ · Lb ∈ Stab(D_b)`. Same proof pattern as the
first component; but note that here the transport uses `Ra · τ · Lb` (not
conjugation), which is equivalent to `⟦Lb⁻¹ · τ · Lb⟧` composed with `⟦Ra · · · Lb⁻¹⟧`
on the H-level. For the descent, we use the `Lb`-conjugate form. -/
private lemma rep_stab_iff_diag_stab' {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ : (GL_pair n).H) :
    τ ∈ (ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H ↔
    (⟨(Lb : GL (Fin n) ℚ)⁻¹ * τ * (Lb : GL (Fin n) ℚ),
        (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Lb.2) τ.2)
          Lb.2⟩ : (GL_pair n).H) ∈
      (ConjAct.toConjAct (diagMat n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H :=
  rep_stab_iff_diag_stab b hb Lb Rb hLR τ

/-- **Reverse well-definedness at the first component.** The asymmetric map
`σ' ↦ Lc · σ' · La⁻¹` descends from `decompQuot(D_a)` to `decompQuot(rep T(a))`.
This is the inverse of `decompQuot_asymm_first_wd`; proved by unfolding the
stabilizer condition to a GL-level H-membership and H-conjugating by `Ra`. -/
private lemma decompQuot_asymm_first_wd_rev {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (La Ra Lc : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ'₁ σ'₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) σ'₁ σ'₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Lc * σ'₁ * La⁻¹) (Lc * σ'₂ * La⁻¹) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n a ha] at hrel
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hrel ⊢
  rw [hLR]
  have := (GL_pair n).H.mul_mem
    ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Ra.2) hrel) Ra.2
  convert this using 1
  push_cast
  group

/-- **Reverse well-definedness at the second component.** The asymmetric map
`τ' ↦ Ra⁻¹ · τ' · Lb⁻¹` descends from `decompQuot(D_b)` to `decompQuot(rep T(b))`.
This is the inverse of `decompQuot_asymm_second_wd`; proved by unfolding the
stabilizer condition to a GL-level H-membership and H-conjugating by `Rb`. -/
private lemma decompQuot_asymm_second_wd_rev {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ'₁ τ'₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) τ'₁ τ'₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Ra⁻¹ * τ'₁ * Lb⁻¹) (Ra⁻¹ * τ'₂ * Lb⁻¹) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n b hb] at hrel
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hrel ⊢
  rw [hLR]
  have := (GL_pair n).H.mul_mem
    ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Rb.2) hrel) Rb.2
  convert this using 1
  push_cast
  group

/-- **Bridge descent at the first-component level.** The asymmetric map
`σ ↦ Lc⁻¹ · σ · La` descends from `decompQuot(rep T(a))` to `decompQuot(D(a))`,
using the stabilizer iff `rep_stab_iff_diag_stab`. The output quotient class
only involves `σ · La` (since Lc⁻¹ is constant in σ, it factors out).

More precisely: if `σ₁ ~_{Stab(rep T(a))} σ₂`, then `Lc⁻¹·σ₁·La ~_{Stab(D_a)}
Lc⁻¹·σ₂·La`. -/
private lemma decompQuot_asymm_first_wd {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (La Ra Lc : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ₁ σ₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) σ₁ σ₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Lc⁻¹ * σ₁ * La) (Lc⁻¹ * σ₂ * La) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n a ha]
  have hsimp : (Lc⁻¹ * σ₁ * La)⁻¹ * (Lc⁻¹ * σ₂ * La) = La⁻¹ * (σ₁⁻¹ * σ₂) * La := by group
  rw [hsimp]
  have := (rep_stab_iff_diag_stab a ha La Ra hLR (σ₁⁻¹ * σ₂)).mp hrel
  convert this using 1

/-- **Bridge descent at the second-component level.** The asymmetric map
`τ ↦ Ra · τ · Lb` descends from `decompQuot(rep T(b))` to `decompQuot(D(b))`:
if `τ₁ ~_{Stab(rep T(b))} τ₂`, then `Ra·τ₁·Lb ~_{Stab(D_b)} Ra·τ₂·Lb`. -/
private lemma decompQuot_asymm_second_wd {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ₁ τ₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) τ₁ τ₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Ra * τ₁ * Lb) (Ra * τ₂ * Lb) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n b hb]
  have hsimp : (Ra * τ₁ * Lb)⁻¹ * (Ra * τ₂ * Lb) = Lb⁻¹ * (τ₁⁻¹ * τ₂) * Lb := by group
  rw [hsimp]
  have := (rep_stab_iff_diag_stab b hb Lb Rb hLR (τ₁⁻¹ * τ₂)).mp hrel
  convert this using 1

/-! ### Rep ↔ diag H-membership transport -/

/-- The rep-level H-membership for `(diag c)⁻¹·σ·(diag a)·τ·(diag b)` transported via
the `L·D·R` decompositions, iff the corresponding diag-level compensated
H-membership. Proof is H-absorption via conjugation by `Rc` (left) and `Rb` (right). -/
private lemma rep_mem_H_iff_compensated_diag_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ)
    (La Ra Lb Rb Lc Rc : (GL_pair n).H)
    (hDecA : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (hDecB : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (hDecC : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ) =
      (Lc : GL (Fin n) ℚ) * diagMat n c * (Rc : GL (Fin n) ℚ))
    (σ τ : (GL_pair n).H) :
    ((HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * σ *
      (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * τ *
      (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H) ↔
    ((diagMat n c)⁻¹ *
      ((Lc⁻¹ * σ * La : (GL_pair n).H) : GL (Fin n) ℚ) * diagMat n a *
      ((Ra * τ * Lb : (GL_pair n).H) : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H) := by
  rw [hDecA, hDecB, hDecC]
  constructor
  · intro h
    have h1 := (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem Rc.2 h) ((GL_pair n).H.inv_mem Rb.2)
    convert h1 using 1
    push_cast
    group
  · intro h
    have h1 := (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Rc.2) h) Rb.2
    convert h1 using 1
    push_cast
    group

/-- The fiber-pair right-coset condition at the `rep T_diag` level equals the
H-membership condition for the GL product. This is the rep-level analogue of
`fiber_diagMat_iff_mem_H`, generalized to arbitrary `Δ`-elements. -/
private lemma fiber_rep_iff_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ)
    (σ τ : (GL_pair n).H) :
    (({(σ : GL (Fin n) ℚ) *
         (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)} : Set _) *
        {(τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)} *
          ((GL_pair n).H : Set (GL (Fin n) ℚ))) ↔
    (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
        (τ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H := by
  rw [Set.singleton_mul_singleton]
  constructor
  · intro h_eq
    have hmem : (σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
        ((τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)) ∈
        ({(HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)} : Set _) *
          ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
      rw [← h_eq]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
    obtain ⟨_, hd_eq, h, hh, hprod⟩ := hmem
    rw [Set.mem_singleton_iff] at hd_eq
    subst hd_eq
    simp only at hprod
    have h_eq_factor : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
        ((σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
          ((τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ))) = h := by
      rw [← hprod]; group
    rw [show (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
          (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) *
          (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
        (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
          ((σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            ((τ : GL (Fin n) ℚ) *
              (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ))) by group, h_eq_factor]
    exact hh
  · intro h_mem
    set h_elt := (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)
    ext y
    constructor
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt * k, (GL_pair n).H.mul_mem h_mem hk, ?_⟩
      simp only [h_elt]; group
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt⁻¹ * k,
        (GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem h_mem) hk, ?_⟩
      simp only [h_elt]; group

/-! ### The compensated bridge injections and the bridge lemma -/

set_option maxHeartbeats 1600000 in
/-- **Bridge ≤ direction.** rep-multiplicity ≤ diagMat-multiplicity via a compensated
injection, paralleling `heckeMultiplicity_block_embed_ge_diagMat`. -/
private lemma heckeMultiplicity_rep_le_diagMat_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) ≤
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) := by
  obtain ⟨La_gl, hLa_mem, Ra_gl, hRa_mem, hDecA⟩ := T_diag_rep_decompose a ha
  obtain ⟨Lb_gl, hLb_mem, Rb_gl, hRb_mem, hDecB⟩ := T_diag_rep_decompose b hb
  obtain ⟨Lc_gl, hLc_mem, Rc_gl, hRc_mem, hDecC⟩ := T_diag_rep_decompose c hc
  set La : (GL_pair n).H := ⟨La_gl, hLa_mem⟩ with La_def
  set Ra : (GL_pair n).H := ⟨Ra_gl, hRa_mem⟩ with Ra_def
  set Lb : (GL_pair n).H := ⟨Lb_gl, hLb_mem⟩ with Lb_def
  set Rb : (GL_pair n).H := ⟨Rb_gl, hRb_mem⟩ with Rb_def
  set Lc : (GL_pair n).H := ⟨Lc_gl, hLc_mem⟩ with Lc_def
  set Rc : (GL_pair n).H := ⟨Rc_gl, hRc_mem⟩ with Rc_def
  have h_dval_a : ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n a :=
    diagMat_delta_val n a ha
  have h_dval_b : ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n b :=
    diagMat_delta_val n b hb
  have h_dval_c : ((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n c :=
    diagMat_delta_val n c hc
  let getN₁ : (GL_pair n).H →
      (ConjAct.toConjAct ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose
  have hgetN₁_spec : ∀ σ : (GL_pair n).H,
      (⟦σ⟧ : decompQuot (GL_pair n) (diagMat_delta n a)).out = σ * getN₁ σ :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose_spec
  let mkYbase : (GL_pair n).H → (GL_pair n).H → (GL_pair n).H :=
    fun σ_bar τ_bar ↦ ⟨_, conjAct_inv_mem_of_subgroupOf
      ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) (getN₁ σ_bar)⟩ * τ_bar
  let SrcType : Type := {p : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ×
            decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b)) |
            ({(p.1.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag a) : (GL_pair n).Δ) : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag b) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {((HeckeCoset.rep (T_diag c) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair n) (diagMat_delta n a) ×
            decompQuot (GL_pair n) (diagMat_delta n b) |
            ({(p.1.out : GL (Fin n) ℚ) *
              (diagMat_delta n a : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              (diagMat_delta n b : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {(diagMat_delta n c : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦Lc⁻¹ * i.out * La⟧,
      ⟦mkYbase (Lc⁻¹ * i.out * La) (Ra * j.out * Lb)⟧),
      by
        have h_rep_mem := (fiber_rep_iff_mem_H a b c i.out j.out).mp hcond
        have h_diag_mem := (rep_mem_H_iff_compensated_diag_mem_H a b c
          La Ra Lb Rb Lc Rc hDecA hDecB hDecC i.out j.out).mp h_rep_mem
        have h_iff_lift := fiber_diagMat_iff_mem_H a b c ha hb hc
          (Lc⁻¹ * i.out * La) (Ra * j.out * Lb)
        have h_rc_lift := h_iff_lift.mpr h_diag_mem
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_rc_lift
        set σ_bar : (GL_pair n).H := Lc⁻¹ * i.out * La with σ_bar_def
        set τ_bar : (GL_pair n).H := Ra * j.out * Lb with τ_bar_def
        set n₁ := getN₁ σ_bar with hn₁_def
        set Yval := mkYbase σ_bar τ_bar with hY_def
        have hi_out_eq :
            ((⟦σ_bar⟧ : decompQuot (GL_pair n) (diagMat_delta n a)).out :
              GL (Fin n) ℚ) =
            (σ_bar : GL (Fin n) ℚ) * (n₁ : GL (Fin n) ℚ) := by
          have h := hgetN₁_spec σ_bar
          have := congr_arg (Subtype.val : ↥(GL_pair n).H → GL (Fin n) ℚ) h
          simpa [Subgroup.coe_mul] using this
        obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) •
            (GL_pair n).H).subgroupOf (GL_pair n).H) Yval
        have hj_out_eq :
            ((⟦Yval⟧ : decompQuot (GL_pair n) (diagMat_delta n b)).out :
              GL (Fin n) ℚ) =
            (Yval : GL (Fin n) ℚ) * (n₂ : GL (Fin n) ℚ) := by
          have := congr_arg (Subtype.val :
            ↥(GL_pair n).H → GL (Fin n) ℚ) hn₂_eq
          simpa [Subgroup.coe_mul] using this
        have hYval_coe : (Yval : GL (Fin n) ℚ) =
            ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ)⁻¹ *
            (n₁ : GL (Fin n) ℚ)⁻¹ *
            ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) *
            (τ_bar : GL (Fin n) ℚ) := by
          show ((mkYbase σ_bar τ_bar : (GL_pair n).H) : GL (Fin n) ℚ) = _
          simp [mkYbase, Subgroup.coe_mul, hn₁_def]
        have hj_form :
            ((⟦Yval⟧ : decompQuot (GL_pair n) (diagMat_delta n b)).out :
              GL (Fin n) ℚ) =
            ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ)⁻¹ *
            (n₁ : GL (Fin n) ℚ)⁻¹ *
            ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) *
            (τ_bar : GL (Fin n) ℚ) * (n₂ : GL (Fin n) ℚ) := by
          rw [hj_out_eq, hYval_coe]
        have hn₂_conj :
            ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ)⁻¹ *
              (n₂ : GL (Fin n) ℚ) *
              ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) ∈ (GL_pair n).H :=
          conjAct_mem_of_subgroupOf _ n₂
        have h_rc_lift_merged :
            ({(σ_bar : GL (Fin n) ℚ) *
                ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) *
                ((τ_bar : GL (Fin n) ℚ) *
                  ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ))} : Set _) *
            ((GL_pair n).H : Set _) =
            {((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _) := by
          rw [← Set.singleton_mul_singleton]; exact h_rc_lift
        have h_target := coset_shift_fwd_q1
          (σ_bar : GL (Fin n) ℚ)
          (τ_bar : GL (Fin n) ℚ)
          ((⟦σ_bar⟧ : decompQuot (GL_pair n) (diagMat_delta n a)).out : GL (Fin n) ℚ)
          ((⟦Yval⟧ : decompQuot (GL_pair n) (diagMat_delta n b)).out : GL (Fin n) ℚ)
          ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ)
          ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ)
          ((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ)
          (n₁ : GL (Fin n) ℚ) (n₂ : GL (Fin n) ℚ)
          h_rc_lift_merged hi_out_eq hj_form hn₂_conj
        rw [← Set.singleton_mul_singleton] at h_target
        exact h_target⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦Lc⁻¹ * i₁.out * La⟧ :
      decompQuot (GL_pair n) (diagMat_delta n a)) =
      ⟦Lc⁻¹ * i₂.out * La⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦mkYbase (Lc⁻¹ * i₁.out * La) (Ra * j₁.out * Lb)⟧ :
      decompQuot (GL_pair n) (diagMat_delta n b)) =
      ⟦mkYbase (Lc⁻¹ * i₂.out * La) (Ra * j₂.out * Lb)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ := by
    rw [Quotient.eq] at h_i_eq
    change QuotientGroup.leftRel _ (Lc⁻¹ * i₁.out * La) (Lc⁻¹ * i₂.out * La) at h_i_eq
    have h_out : (⟦i₁.out⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))) =
        ⟦i₂.out⟧ := by
      apply Quotient.sound
      change QuotientGroup.leftRel _ i₁.out i₂.out
      rw [QuotientGroup.leftRel_apply]
      have h_rev := decompQuot_asymm_first_wd_rev (n := n) a ha La Ra Lc hDecA
        (Lc⁻¹ * i₁.out * La) (Lc⁻¹ * i₂.out * La) h_i_eq
      rw [QuotientGroup.leftRel_apply] at h_rev
      have h_simp : (Lc * (Lc⁻¹ * i₁.out * La) * La⁻¹)⁻¹ *
          (Lc * (Lc⁻¹ * i₂.out * La) * La⁻¹) = i₁.out⁻¹ * i₂.out := by group
      rw [h_simp] at h_rev
      exact h_rev
    calc i₁ = (⟦i₁.out⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))) :=
          (decompQuot_out_eq i₁).symm
      _ = ⟦i₂.out⟧ := h_out
      _ = i₂ := decompQuot_out_eq i₂
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (diagMat_delta n b)
    ⟨_, conjAct_inv_mem_of_subgroupOf
      ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ)
      (getN₁ (Lc⁻¹ * i₁.out * La))⟩
    (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) h_j_eq
  have h_j_final : j₁ = j₂ := by
    rw [Quotient.eq] at h_j_cancel
    change QuotientGroup.leftRel _ (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) at h_j_cancel
    have h_out : (⟦j₁.out⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))) =
        ⟦j₂.out⟧ := by
      apply Quotient.sound
      change QuotientGroup.leftRel _ j₁.out j₂.out
      rw [QuotientGroup.leftRel_apply]
      have h_rev := decompQuot_asymm_second_wd_rev (n := n) b hb Lb Rb Ra hDecB
        (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) h_j_cancel
      rw [QuotientGroup.leftRel_apply] at h_rev
      have h_simp : (Ra⁻¹ * (Ra * j₁.out * Lb) * Lb⁻¹)⁻¹ *
          (Ra⁻¹ * (Ra * j₂.out * Lb) * Lb⁻¹) = j₁.out⁻¹ * j₂.out := by group
      rw [h_simp] at h_rev
      exact h_rev
    calc j₁ = (⟦j₁.out⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))) :=
          (decompQuot_out_eq j₁).symm
      _ = ⟦j₂.out⟧ := h_out
      _ = j₂ := decompQuot_out_eq j₂
  subst h_j_final
  rfl

set_option maxHeartbeats 1600000 in
/-- **Bridge ≥ direction.** diagMat-multiplicity ≤ rep-multiplicity via a compensated
injection, symmetric to `heckeMultiplicity_rep_le_diagMat_delta` with the reverse
L/R-compensation: `σ' ↦ Lc · σ' · La⁻¹`, `τ' ↦ Ra⁻¹ · τ' · Lb⁻¹`. -/
private lemma heckeMultiplicity_diagMat_le_rep_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) ≤
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) := by
  obtain ⟨La_gl, hLa_mem, Ra_gl, hRa_mem, hDecA⟩ := T_diag_rep_decompose a ha
  obtain ⟨Lb_gl, hLb_mem, Rb_gl, hRb_mem, hDecB⟩ := T_diag_rep_decompose b hb
  obtain ⟨Lc_gl, hLc_mem, Rc_gl, hRc_mem, hDecC⟩ := T_diag_rep_decompose c hc
  set La : (GL_pair n).H := ⟨La_gl, hLa_mem⟩ with La_def
  set Ra : (GL_pair n).H := ⟨Ra_gl, hRa_mem⟩ with Ra_def
  set Lb : (GL_pair n).H := ⟨Lb_gl, hLb_mem⟩ with Lb_def
  set Rb : (GL_pair n).H := ⟨Rb_gl, hRb_mem⟩ with Rb_def
  set Lc : (GL_pair n).H := ⟨Lc_gl, hLc_mem⟩ with Lc_def
  set Rc : (GL_pair n).H := ⟨Rc_gl, hRc_mem⟩ with Rc_def
  have h_dval_a : ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n a :=
    diagMat_delta_val n a ha
  have h_dval_b : ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n b :=
    diagMat_delta_val n b hb
  have h_dval_c : ((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n c :=
    diagMat_delta_val n c hc
  let getN₁ : (GL_pair n).H →
      (ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose
  have hgetN₁_spec : ∀ σ : (GL_pair n).H,
      (⟦σ⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))).out = σ * getN₁ σ :=
    fun σ ↦ (QuotientGroup.mk_out_eq_mul _ σ).choose_spec
  let mkYbase : (GL_pair n).H → (GL_pair n).H → (GL_pair n).H :=
    fun σ_bar τ_bar ↦ ⟨_, conjAct_inv_mem_of_subgroupOf
      (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) (getN₁ σ_bar)⟩ * τ_bar
  let SrcType : Type := {p : decompQuot (GL_pair n) (diagMat_delta n a) ×
            decompQuot (GL_pair n) (diagMat_delta n b) |
            ({(p.1.out : GL (Fin n) ℚ) *
              (diagMat_delta n a : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              (diagMat_delta n b : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {(diagMat_delta n c : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ×
            decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b)) |
            ({(p.1.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag a) : (GL_pair n).Δ) : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag b) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {((HeckeCoset.rep (T_diag c) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦Lc * i.out * La⁻¹⟧,
      ⟦mkYbase (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)⟧),
      by
        have h_iff := fiber_diagMat_iff_mem_H a b c ha hb hc i.out j.out
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_iff
        have h_diag_mem_pre := h_iff.mp hcond
        have h_diag_mem : (diagMat n c)⁻¹ * (i.out : GL (Fin n) ℚ) * diagMat n a *
            (j.out : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H := by
          convert h_diag_mem_pre using 2 <;> simp [h_dval_a, h_dval_b, h_dval_c]
        have h_rep_mem : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
            ((Lc * i.out * La⁻¹ : (GL_pair n).H) : GL (Fin n) ℚ) *
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            ((Ra⁻¹ * j.out * Lb⁻¹ : (GL_pair n).H) : GL (Fin n) ℚ) *
            (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H := by
          apply (rep_mem_H_iff_compensated_diag_mem_H a b c La Ra Lb Rb Lc Rc
            hDecA hDecB hDecC (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)).mpr
          have h_simp_i : (Lc⁻¹ * (Lc * i.out * La⁻¹) * La : (GL_pair n).H) = i.out := by
            group
          have h_simp_j : (Ra * (Ra⁻¹ * j.out * Lb⁻¹) * Lb : (GL_pair n).H) = j.out := by
            group
          rw [h_simp_i, h_simp_j]
          exact h_diag_mem
        have h_iff_lift := fiber_rep_iff_mem_H a b c
          (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)
        have h_rc_lift := h_iff_lift.mpr h_rep_mem
        set σ_bar : (GL_pair n).H := Lc * i.out * La⁻¹ with σ_bar_def
        set τ_bar : (GL_pair n).H := Ra⁻¹ * j.out * Lb⁻¹ with τ_bar_def
        set n₁ := getN₁ σ_bar with hn₁_def
        set Yval := mkYbase σ_bar τ_bar with hY_def
        have hi_out_eq :
            ((⟦σ_bar⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))).out :
              GL (Fin n) ℚ) =
            (σ_bar : GL (Fin n) ℚ) * (n₁ : GL (Fin n) ℚ) := by
          have h := hgetN₁_spec σ_bar
          have := congr_arg (Subtype.val : ↥(GL_pair n).H → GL (Fin n) ℚ) h
          simpa [Subgroup.coe_mul] using this
        obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
            (GL_pair n).H).subgroupOf (GL_pair n).H) Yval
        have hj_out_eq :
            ((⟦Yval⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))).out :
              GL (Fin n) ℚ) =
            (Yval : GL (Fin n) ℚ) * (n₂ : GL (Fin n) ℚ) := by
          have := congr_arg (Subtype.val :
            ↥(GL_pair n).H → GL (Fin n) ℚ) hn₂_eq
          simpa [Subgroup.coe_mul] using this
        have hYval_coe : (Yval : GL (Fin n) ℚ) =
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)⁻¹ *
            (n₁ : GL (Fin n) ℚ)⁻¹ *
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            (τ_bar : GL (Fin n) ℚ) := by
          show ((mkYbase σ_bar τ_bar : (GL_pair n).H) : GL (Fin n) ℚ) = _
          simp [mkYbase, Subgroup.coe_mul, hn₁_def]
        have hj_form :
            ((⟦Yval⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))).out :
              GL (Fin n) ℚ) =
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)⁻¹ *
            (n₁ : GL (Fin n) ℚ)⁻¹ *
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            (τ_bar : GL (Fin n) ℚ) * (n₂ : GL (Fin n) ℚ) := by
          rw [hj_out_eq, hYval_coe]
        have hn₂_conj :
            (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)⁻¹ *
              (n₂ : GL (Fin n) ℚ) *
              (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H :=
          conjAct_mem_of_subgroupOf _ n₂
        have h_rc_lift_merged :
            ({(σ_bar : GL (Fin n) ℚ) *
                (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
                ((τ_bar : GL (Fin n) ℚ) *
                  (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ))} : Set _) *
            ((GL_pair n).H : Set _) =
            {(HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _) := by
          rw [← Set.singleton_mul_singleton]; exact h_rc_lift
        have h_target := coset_shift_fwd_q1
          (σ_bar : GL (Fin n) ℚ)
          (τ_bar : GL (Fin n) ℚ)
          ((⟦σ_bar⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))).out :
            GL (Fin n) ℚ)
          ((⟦Yval⟧ : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))).out :
            GL (Fin n) ℚ)
          (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)
          (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)
          (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)
          (n₁ : GL (Fin n) ℚ) (n₂ : GL (Fin n) ℚ)
          h_rc_lift_merged hi_out_eq hj_form hn₂_conj
        rw [← Set.singleton_mul_singleton] at h_target
        exact h_target⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦Lc * i₁.out * La⁻¹⟧ :
      decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))) =
      ⟦Lc * i₂.out * La⁻¹⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦mkYbase (Lc * i₁.out * La⁻¹) (Ra⁻¹ * j₁.out * Lb⁻¹)⟧ :
      decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))) =
      ⟦mkYbase (Lc * i₂.out * La⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ := by
    rw [Quotient.eq] at h_i_eq
    change QuotientGroup.leftRel _ (Lc * i₁.out * La⁻¹) (Lc * i₂.out * La⁻¹) at h_i_eq
    have h_out : (⟦i₁.out⟧ : decompQuot (GL_pair n) (diagMat_delta n a)) =
        ⟦i₂.out⟧ := by
      apply Quotient.sound
      change QuotientGroup.leftRel _ i₁.out i₂.out
      rw [QuotientGroup.leftRel_apply]
      have h_fwd := decompQuot_asymm_first_wd (n := n) a ha La Ra Lc hDecA
        (Lc * i₁.out * La⁻¹) (Lc * i₂.out * La⁻¹) h_i_eq
      rw [QuotientGroup.leftRel_apply] at h_fwd
      have h_simp : (Lc⁻¹ * (Lc * i₁.out * La⁻¹) * La)⁻¹ *
          (Lc⁻¹ * (Lc * i₂.out * La⁻¹) * La) = i₁.out⁻¹ * i₂.out := by group
      rw [h_simp] at h_fwd
      exact h_fwd
    calc i₁ = (⟦i₁.out⟧ : decompQuot (GL_pair n) (diagMat_delta n a)) :=
          (decompQuot_out_eq i₁).symm
      _ = ⟦i₂.out⟧ := h_out
      _ = i₂ := decompQuot_out_eq i₂
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (HeckeCoset.rep (T_diag b))
    ⟨_, conjAct_inv_mem_of_subgroupOf
      (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)
      (getN₁ (Lc * i₁.out * La⁻¹))⟩
    (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹) h_j_eq
  have h_j_final : j₁ = j₂ := by
    rw [Quotient.eq] at h_j_cancel
    change QuotientGroup.leftRel _ (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹)
      at h_j_cancel
    have h_out : (⟦j₁.out⟧ : decompQuot (GL_pair n) (diagMat_delta n b)) =
        ⟦j₂.out⟧ := by
      apply Quotient.sound
      change QuotientGroup.leftRel _ j₁.out j₂.out
      rw [QuotientGroup.leftRel_apply]
      have h_fwd := decompQuot_asymm_second_wd (n := n) b hb Lb Rb Ra hDecB
        (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹) h_j_cancel
      rw [QuotientGroup.leftRel_apply] at h_fwd
      have h_simp : (Ra * (Ra⁻¹ * j₁.out * Lb⁻¹) * Lb)⁻¹ *
          (Ra * (Ra⁻¹ * j₂.out * Lb⁻¹) * Lb) = j₁.out⁻¹ * j₂.out := by group
      rw [h_simp] at h_fwd
      exact h_fwd
    calc j₁ = (⟦j₁.out⟧ : decompQuot (GL_pair n) (diagMat_delta n b)) :=
          (decompQuot_out_eq j₁).symm
      _ = ⟦j₂.out⟧ := h_out
      _ = j₂ := decompQuot_out_eq j₂
  subst h_j_final
  rfl

/-- **Bridge lemma.** The Hecke multiplicity at `rep T_diag` level equals the
multiplicity at `diagMat_delta` level. Proved by two compensated injections
(`heckeMultiplicity_rep_le_diagMat_delta` and `heckeMultiplicity_diagMat_le_rep_delta`)
combined via `le_antisymm`. -/
private lemma heckeMultiplicity_rep_eq_diagMat_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) =
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) :=
  le_antisymm (heckeMultiplicity_rep_le_diagMat_delta a b c ha hb hc)
    (heckeMultiplicity_diagMat_le_rep_delta a b c ha hb hc)

/-! ### Diagonal-level ≤ direction (Shimura Lemma 3.19 hard half)

The harder half of Shimura's Lemma 3.19: injection `Fiber_{k+2}^{cons1} → Fiber_{k+1}`.
Proof requires the lattice projection `M' ↦ M = M' ∩ L'` via the quotient-level
normalization: any fiber pair at dim `k+2` has `slSuccEmbed_H`-preimages satisfying
the dim-`k+1` fiber condition. Formally isolated as `fiber_block_form_preimage`
below; currently stated but not proved.

The mathematical core (Shimura p. 59, bottom): given `σ, τ ∈ SL_{k+2}(ℤ)` in a fiber
pair at dim `k+2` with `Fin.cons 1 _` diagonals, there exist equivalent representatives
`σ̃ ~ σ`, `τ̃ ~ τ` (mod the respective stabilizers) such that `σ̃, τ̃` both have
block form `1 ⊕ σ_m`, `1 ⊕ τ_m`, and `(σ_m, τ_m)` forms a fiber pair at dim `k+1`. -/

/-- **First column of `SL_n(ℤ)` is primitive.** Any common integer divisor of
the entries of column 0 of an `SL_n(ℤ)` matrix is a unit (`±1`). Follows from
Laplace expansion of the determinant along column 0. -/
private lemma sl_first_col_primitive {n : ℕ} [NeZero n]
    (N : SpecialLinearGroup (Fin n) ℤ) (d : ℤ)
    (hd : ∀ i, d ∣ N.1 i 0) : IsUnit d := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_column_zero]
    refine Finset.dvd_sum fun i _ ↦ ?_
    exact ((hd i).mul_left _).mul_right _
  rw [show N.1.det = 1 from N.2] at h_dvd_det
  exact isUnit_of_dvd_one h_dvd_det

/-- **Row primitivity for `SL_n(ℤ)`.** Any common integer divisor of the entries
of an arbitrary row `r` of an `SL_n(ℤ)` matrix is a unit (`±1`). Follows from
Laplace expansion of the determinant along row `r`. -/
private lemma sl_row_primitive {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (d : ℤ) (hd : ∀ k : Fin n.succ, d ∣ N.1 r k) : IsUnit d := by
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_row N.1 r]
    refine Finset.dvd_sum fun j _ ↦ ?_
    exact ((hd j).mul_left _).mul_right _
  rw [show N.1.det = 1 from N.2] at h_dvd_det
  exact isUnit_of_dvd_one h_dvd_det

/-- **Row non-divisibility by a non-unit.** If `p : ℤ` is not a unit, then for
any row `r` of `N ∈ SL_n(ℤ)` there is some column `k` with `p ∤ N.1 r k`.
Direct contrapositive of `sl_row_primitive`. -/
private lemma sl_row_exists_not_dvd {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (p : ℤ) (hp_not_unit : ¬ IsUnit p) :
    ∃ k : Fin n.succ, ¬ p ∣ N.1 r k := by
  by_contra h
  push_neg at h
  exact hp_not_unit (sl_row_primitive N r p h)

/-- **Row non-divisibility by a prime divisor of `m`.** If `p : ℕ` is a prime
dividing `m.natAbs`, then for any row `r` of `N ∈ SL_n(ℤ)` there is some column
`k` with `(p : ℤ) ∤ N.1 r k`. -/
private lemma sl_row_exists_not_dvd_of_prime {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ) (r : Fin n.succ)
    (p : ℕ) (hp : p.Prime) :
    ∃ k : Fin n.succ, ¬ (p : ℤ) ∣ N.1 r k := by
  refine sl_row_exists_not_dvd N r (p : ℤ) ?_
  intro h_unit
  have h := Int.isUnit_iff.mp h_unit
  rcases h with h | h
  · have hp1 : p = 1 := by exact_mod_cast h
    exact hp.one_lt.ne' hp1
  · have : (p : ℤ) ≥ 0 := Int.natCast_nonneg _
    have hpos : (p : ℤ) > 0 := by exact_mod_cast hp.pos
    linarith

/-- **Row Bezout coefficients for `SL_n(ℤ)`.** For any row `r` of an
`SL_n(ℤ)` matrix, there exist integer coefficients `c k` such that
`∑ k, c k * N.1 r k = 1`. Take `c k` to be the signed `(r,k)`-minor; then
the sum is exactly the Laplace expansion of `det N = 1` along row `r`. -/
private lemma sl_row_bezout {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) :
    ∃ c : Fin n.succ → ℤ, ∑ k, c k * N.1 r k = 1 := by
  refine ⟨fun k ↦ (-1) ^ ((r : ℕ) + (k : ℕ)) *
    (N.1.submatrix r.succAbove k.succAbove).det, ?_⟩
  have hdet : N.1.det = 1 := N.2
  rw [Matrix.det_succ_row N.1 r] at hdet
  have h_eq : ∑ k : Fin n.succ, ((-1) ^ ((r : ℕ) + (k : ℕ)) *
      (N.1.submatrix r.succAbove k.succAbove).det) * N.1 r k =
      ∑ j : Fin n.succ, (-1) ^ ((r : ℕ) + (j : ℕ)) * N.1 r j *
        (N.1.submatrix r.succAbove j.succAbove).det :=
    Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h_eq, hdet]

/-- **Row clearing modulo `m`.** From `sl_row_bezout`, for any target value
`x` and modulus `m` we can find coefficients `c` with
`m ∣ x + ∑ k, c k * N.1 r k`. The construction takes `c k := -x · c₀ k`
where `c₀` are the Bezout coefficients, making the sum `-x` so that
`x + (-x) = 0` is divisible by any `m`. -/
private lemma sl_row_clear_mod {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (x m : ℤ) :
    ∃ c : Fin n.succ → ℤ, m ∣ x + ∑ k, c k * N.1 r k := by
  obtain ⟨c₀, hc₀⟩ := sl_row_bezout N r
  refine ⟨fun k ↦ -x * c₀ k, ?_⟩
  have h_sum : ∑ k, (-x * c₀ k) * N.1 r k = -x := by
    have : ∑ k, (-x * c₀ k) * N.1 r k = -x * ∑ k, c₀ k * N.1 r k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hc₀, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

/-- **Row clearing modulo `m`, avoiding column `k₀`.** When the row entries
of `N` excluding column `k₀` already generate the unit ideal (hypothesis
`h_redundant`), we can pick Bezout coefficients with `c k₀ = 0`. The proof
constructs a modified matrix-style argument by passing through any
unit-witness from the redundant entries. -/
private lemma sl_row_clear_mod_avoiding {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (k₀ : Fin n.succ)
    (h_redundant : ∃ c₀ : Fin n.succ → ℤ,
      c₀ k₀ = 0 ∧ ∑ k, c₀ k * N.1 r k = 1)
    (x m : ℤ) :
    ∃ c : Fin n.succ → ℤ, c k₀ = 0 ∧ m ∣ x + ∑ k, c k * N.1 r k := by
  obtain ⟨c₀, hc₀_zero, hc₀_sum⟩ := h_redundant
  refine ⟨fun k ↦ -x * c₀ k, by simp [hc₀_zero], ?_⟩
  have h_sum : ∑ k, (-x * c₀ k) * N.1 r k = -x := by
    have : ∑ k, (-x * c₀ k) * N.1 r k = -x * ∑ k, c₀ k * N.1 r k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hc₀_sum, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

/-- **SL(2)-Bezout row operation**: Given integers `a, b` not both zero, there
exists `B ∈ SL(2, ℤ)` whose `mulVec` action on `![a, b]` zeros the second
entry, leaving `Int.gcd a b` in the first entry. The explicit construction uses
Bezout coefficients `Int.gcdA`, `Int.gcdB` and the quotients `a / gcd`,
`b / gcd`. The `a ≠ 0 ∨ b ≠ 0` hypothesis rules out the degenerate zero-gcd
case where the quotient-by-gcd formula is invalid. -/
private lemma sl2_bezout_zero_out (a b : ℤ) (h_ne : a ≠ 0 ∨ b ≠ 0) :
    ∃ B : SpecialLinearGroup (Fin 2) ℤ,
      B.1 *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  have hd_ne : (Int.gcd a b : ℤ) ≠ 0 := by
    intro h
    have h_nat : Int.gcd a b = 0 := by exact_mod_cast h
    rcases Int.gcd_eq_zero_iff.mp h_nat with ⟨ha, hb⟩
    rcases h_ne with ha' | hb'
    · exact ha' ha
    · exact hb' hb
  obtain ⟨a', ha'⟩ : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  have h_det : Int.gcdA a b * a' + Int.gcdB a b * b' = 1 := by
    have hprod : (Int.gcd a b : ℤ) * (Int.gcdA a b * a' + Int.gcdB a b * b') =
        (Int.gcd a b : ℤ) * 1 := by
      calc (Int.gcd a b : ℤ) * (Int.gcdA a b * a' + Int.gcdB a b * b')
          = Int.gcdA a b * ((Int.gcd a b : ℤ) * a') +
              Int.gcdB a b * ((Int.gcd a b : ℤ) * b') := by ring
        _ = a * Int.gcdA a b + b * Int.gcdB a b := by rw [← ha', ← hb']; ring
        _ = (Int.gcd a b : ℤ) := hbez.symm
        _ = (Int.gcd a b : ℤ) * 1 := by ring
    exact mul_left_cancel₀ hd_ne hprod
  refine ⟨⟨!![Int.gcdA a b, Int.gcdB a b; -b', a'], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · -- Compute both entries of `B.1 *ᵥ ![a, b]` via `Matrix.mulVec_cons` unfolding.
    have hentries : (!![Int.gcdA a b, Int.gcdB a b; -b', a'] *ᵥ ![a, b] : Fin 2 → ℤ) =
        ![Int.gcdA a b * a + Int.gcdB a b * b, -b' * a + a' * b] := by
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    show (!![Int.gcdA a b, Int.gcdB a b; -b', a'] *ᵥ ![a, b] : Fin 2 → ℤ) =
      ![(Int.gcd a b : ℤ), 0]
    rw [hentries]
    have h0 : Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ) := by
      rw [mul_comm (Int.gcdA a b) a, mul_comm (Int.gcdB a b) b]
      exact hbez.symm
    have h1 : -b' * a + a' * b = 0 := by
      have step : -b' * ((Int.gcd a b : ℤ) * a') + a' * ((Int.gcd a b : ℤ) * b') = 0 := by ring
      rw [← ha', ← hb'] at step
      exact step
    ext i
    fin_cases i
    · change Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ); exact h0
    · change -b' * a + a' * b = 0; exact h1

/-- **Row-embedding helper**: a `2 × 2` SL matrix `B` is lifted into
`SL(Fin (n + 3), ℤ)` acting as `B` on the first two rows/columns and as the
identity on the remaining `n + 1` rows/columns. Follows the `slSuccEmbed`
pattern using `Matrix.fromBlocks` + `submatrix` over the equivalence
`Fin (n + 3) ≃ Fin 2 ⊕ Fin (n + 1)`. -/
private noncomputable def sl2_row_embed_01 {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  let e : Fin (n + 3) ≃ Fin 2 ⊕ Fin (n + 1) :=
    (Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  ⟨(Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix e e, by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one, B.2]⟩

/-- Explicit underlying-matrix form for `sl2_row_embed_01 B`, parameterised
over the reindex equivalence `e`. -/
private lemma sl2_row_embed_01_val_eq {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    (sl2_row_embed_01 (n := n) B).1 =
      (Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm)
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm) := rfl

/-- For `i : Fin (n + 3)` with `i.val < 2`, the block-split equivalence sends `i`
to `Sum.inl ⟨i.val, h⟩`. -/
private lemma sl2_row_embed_01_equiv_lt_2 {n : ℕ} (i : Fin (n + 3)) (h : i.val < 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inl ⟨i.val, h⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.castAdd (n + 1) ⟨i.val, h⟩ := by
    ext; simp [Fin.castAdd]
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_castAdd]

/-- For `i : Fin (n + 3)` with `2 ≤ i.val`, the block-split equivalence sends `i`
to `Sum.inr ⟨i.val - 2, _⟩`. -/
private lemma sl2_row_embed_01_equiv_ge_2 {n : ℕ} (i : Fin (n + 3)) (h : 2 ≤ i.val) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inr ⟨i.val - 2, by omega⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.natAdd 2 ⟨i.val - 2, by omega⟩ := by
    ext; simp [Fin.natAdd]; omega
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_natAdd]

/-- Helper for entry-access of the inverse of the embedding equivalence at
`Sum.inl` indices. -/
private lemma sl2_row_embed_01_equiv_symm_inl {n : ℕ} (j : Fin 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inl j) = ⟨j.val, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.castAdd]

/-- Helper for entry-access of the inverse of the embedding equivalence at
`Sum.inr` indices. -/
private lemma sl2_row_embed_01_equiv_symm_inr {n : ℕ} (j : Fin (n + 1)) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inr j) = ⟨j.val + 2, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.natAdd]
  omega

/-- **`mulVec` action of `sl2_row_embed_01 B`**: The `SL(Fin (n+3), ℤ)` matrix
acts as `B` on the first two entries of `v` and as the identity on entries of
index `≥ 2`. -/
private lemma sl2_row_embed_01_mulVec {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ)
    (v : Fin (n + 3) → ℤ) (i : Fin (n + 3)) :
    ((sl2_row_embed_01 B).1 *ᵥ v) i =
      if h : i.val < 2 then (B.1 *ᵥ ![v 0, v 1]) ⟨i.val, h⟩ else v i := by
  rw [sl2_row_embed_01_val_eq, Matrix.submatrix_mulVec_equiv]
  by_cases h : i.val < 2
  · simp only [h, dite_true, Function.comp_apply]
    rw [sl2_row_embed_01_equiv_lt_2 i h, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero]
    have h_restrict : ((v ∘ ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm).symm) ∘ Sum.inl : Fin 2 → ℤ) = ![v 0, v 1] := by
      funext j
      fin_cases j <;>
        · simp only [Function.comp_apply]
          rw [sl2_row_embed_01_equiv_symm_inl]
          rfl
    rw [h_restrict]
  · simp only [h, dite_false, Function.comp_apply]
    have h' : 2 ≤ i.val := Nat.not_lt.mp h
    rw [sl2_row_embed_01_equiv_ge_2 i h', Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Matrix.zero_mulVec, zero_add,
      Matrix.one_mulVec, Function.comp_apply]
    rw [sl2_row_embed_01_equiv_symm_inr]
    apply congr_arg
    apply Fin.ext
    show (i.val - 2) + 2 = i.val
    omega


/-- **Bezout reduction at dim `n + 3`**: given a primitive-ready vector
`w : Fin (n + 3) → ℤ` with `w 0` or `w 1` nonzero, there exists an
`SL(Fin (n + 3), ℤ)` matrix `E` such that `E *ᵥ w` has the form
`(gcd (w 0) (w 1), 0, w 2, w 3, …, w_{n+2})` — second entry zeroed, first
entry is the gcd, and entries from index 2 onward are unchanged. This bundles
the Bezout `SL(2)` move + row embedding into the form used by the Helper A
induction step to descend to dim `n + 2`. -/
private lemma sl_bezout_reduce_dim {n : ℕ} (w : Fin (n + 3) → ℤ)
    (h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0) :
    ∃ E : SpecialLinearGroup (Fin (n + 3)) ℤ,
      (E.1 *ᵥ w) 0 = (Int.gcd (w 0) (w 1) : ℤ) ∧
      (E.1 *ᵥ w) 1 = 0 ∧
      (∀ i : Fin (n + 1), (E.1 *ᵥ w) ⟨i.val + 2, by omega⟩ =
        w ⟨i.val + 2, by omega⟩) := by
  obtain ⟨B, hB⟩ := sl2_bezout_zero_out (w 0) (w 1) h_ne
  refine ⟨sl2_row_embed_01 (n := n) B, ?_, ?_, ?_⟩
  · -- (E *ᵥ w) 0 = (B *ᵥ ![w 0, w 1]) 0 = (![gcd, 0]) 0 = gcd
    rw [sl2_row_embed_01_mulVec]
    have h0 : (0 : Fin (n + 3)).val < 2 := by show 0 < 2; omega
    simp only [h0, dite_true]
    rw [hB]
    rfl
  · rw [sl2_row_embed_01_mulVec]
    have h1 : (1 : Fin (n + 3)).val < 2 := by show 1 < 2; omega
    simp only [h1, dite_true]
    rw [hB]
    rfl
  · intro i
    rw [sl2_row_embed_01_mulVec]
    have hge : ¬ (⟨i.val + 2, by omega⟩ : Fin (n + 3)).val < 2 := by
      show ¬ (i.val + 2 < 2); omega
    simp only [hge, dite_false]

/-- **Primitivity transfer through SL action**: if `d` divides every entry of
`M.1 *ᵥ v`, then `d` divides every entry of `v`. Follows from `M⁻¹ * M = 1`
and the fact that `M⁻¹` has integer entries. -/
private lemma sl_dvd_of_mulVec_dvd {m : ℕ} (M : SpecialLinearGroup (Fin m) ℤ)
    (v : Fin m → ℤ) (d : ℤ) (h : ∀ i, d ∣ (M.1 *ᵥ v) i) (i : Fin m) : d ∣ v i := by
  have h_inv_mul : (M⁻¹).1 * M.1 = (1 : Matrix (Fin m) (Fin m) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
  have hv_eq : v i = ((M⁻¹).1 *ᵥ (M.1 *ᵥ v)) i := by
    rw [Matrix.mulVec_mulVec, h_inv_mul, Matrix.one_mulVec]
  rw [hv_eq]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum (fun k _ ↦ (h k).mul_left _)

/-- **Extension helper**: lift `M : SL(Fin (n + 2), ℤ)` to `SL(Fin (n + 3), ℤ)`
by inserting an identity row and column at index 1. Built from `slSuccEmbed M`
(which inserts identity at index 0) plus the swap permutation on 0, 1. -/
private noncomputable def sl_extend_at_1 {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  ⟨(slSuccEmbed M).1.submatrix (Equiv.swap (0 : Fin (n + 3)) 1) (Equiv.swap 0 1), by
    rw [det_submatrix_equiv_self]; exact (slSuccEmbed M).2⟩

/-- Entry-0 column values of `sl_extend_at_1 M`: at row 0, get `M.1 0 0`;
at row 1, get 0; at row `i+2` (for `i : Fin (n+1)`), get `M.1 (i.val + 1) 0`. -/
private lemma sl_extend_at_1_col_0_zero {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    (sl_extend_at_1 M).1 0 0 = M.1 0 0 := by
  show (slSuccEmbed M).1 (Equiv.swap 0 1 0) (Equiv.swap 0 1 0) = M.1 0 0
  rw [Equiv.swap_apply_left]
  exact slSuccEmbed_val_succ_succ M 0 0

private lemma sl_extend_at_1_col_0_one {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    (sl_extend_at_1 M).1 1 0 = 0 := by
  show (slSuccEmbed M).1 (Equiv.swap (0 : Fin (n + 3)) 1 1) (Equiv.swap (0 : Fin (n + 3)) 1 0) = 0
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  exact slSuccEmbed_val_zero_succ M 0

private lemma sl_extend_at_1_col_0_ge_2 {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ)
    (i : Fin (n + 1)) :
    (sl_extend_at_1 M).1 ⟨i.val + 2, by omega⟩ 0 = M.1 ⟨i.val + 1, by omega⟩ 0 := by
  show (slSuccEmbed M).1 (Equiv.swap 0 1 ⟨i.val + 2, by omega⟩) (Equiv.swap 0 1 0) = _
  have h_ne_0 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) ≠ 0 := by
    apply Fin.ne_of_val_ne; simp
  have h_ne_1 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) ≠ 1 := by
    apply Fin.ne_of_val_ne; show i.val + 2 ≠ 1; omega
  rw [Equiv.swap_apply_of_ne_of_ne h_ne_0 h_ne_1, Equiv.swap_apply_left]
  have : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)).succ := by
    apply Fin.ext; rfl
  rw [this, show (1 : Fin (n + 3)) = (0 : Fin (n + 2)).succ from rfl,
      slSuccEmbed_val_succ_succ]

/-- **Vector/column comparison**: connects `sl_extend_at_1 N'` to a
`sl_bezout_reduce_dim` output. Given an IH-supplied `N' : SL(Fin (n+2), ℤ)`
with first column `w'` (where `w' 0 = gcd(w_ok 0, w_ok 1)` and
`w' ⟨i+1, _⟩ = w_ok ⟨i+2, _⟩`), the col-0 entry of `sl_extend_at_1 N'` at any
`i : Fin (n+3)` matches the `i`-th entry of `E.1 *ᵥ w_ok` from
`sl_bezout_reduce_dim`. -/
private lemma sl_extend_at_1_col_0_matches_reduce {n : ℕ}
    (w_ok : Fin (n + 3) → ℤ) (w' : Fin (n + 2) → ℤ)
    (N' : SpecialLinearGroup (Fin (n + 2)) ℤ)
    (hN' : ∀ i, N'.1 i 0 = w' i)
    (hw'_0 : w' 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ))
    (hw'_succ : ∀ i : Fin (n + 1), w' ⟨i.val + 1, by omega⟩ =
      w_ok ⟨i.val + 2, by omega⟩)
    (E : SpecialLinearGroup (Fin (n + 3)) ℤ)
    (hE0 : (E.1 *ᵥ w_ok) 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ))
    (hE1 : (E.1 *ᵥ w_ok) 1 = 0)
    (hErest : ∀ i : Fin (n + 1), (E.1 *ᵥ w_ok) ⟨i.val + 2, by omega⟩ =
      w_ok ⟨i.val + 2, by omega⟩) :
    ∀ i : Fin (n + 3), (sl_extend_at_1 N').1 i 0 = (E.1 *ᵥ w_ok) i := by
  intro i
  by_cases h0 : i.val = 0
  · have hi_eq : i = 0 := Fin.ext h0
    rw [hi_eq, sl_extend_at_1_col_0_zero, hE0, hN' 0, hw'_0]
  · by_cases h1 : i.val = 1
    · have hi_eq : i = 1 := Fin.ext h1
      rw [hi_eq, sl_extend_at_1_col_0_one, hE1]
    · have h_ge : 2 ≤ i.val := by omega
      have h_lt : i.val < n + 3 := i.isLt
      let i' : Fin (n + 1) := ⟨i.val - 2, by omega⟩
      have hi_eq : i = ⟨i'.val + 2, by omega⟩ := by
        apply Fin.ext
        show i.val = i.val - 2 + 2
        omega
      rw [hi_eq, sl_extend_at_1_col_0_ge_2 N' i', hErest i',
          hN' ⟨i'.val + 1, by omega⟩, hw'_succ i']

/-- **Primitive 2-vector completion to `SL(2, ℤ)`**. Given a primitive integer
vector `w : Fin 2 → ℤ` (any common divisor is a unit), there exists
`N ∈ SL(2, ℤ)` with `N.col 0 = w`. The `Fin 2` base case of the general
primitive-column-completion helper, derived from `IsCoprime.exists_SL2_col`. -/
private lemma sl_exists_col_of_primitive_fin_2 (w : Fin 2 → ℤ)
    (hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d) :
    ∃ N : SpecialLinearGroup (Fin 2) ℤ, ∀ i, N.1 i 0 = w i := by
  have hcop : IsCoprime (w 0) (w 1) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h_dvd : ∀ i : Fin 2, (Int.gcd (w 0) (w 1) : ℤ) ∣ w i := by
      intro i
      fin_cases i
      · exact Int.gcd_dvd_left _ _
      · exact Int.gcd_dvd_right _ _
    have hunit := hw _ h_dvd
    rcases Int.isUnit_iff.mp hunit with hpos | hneg
    · exact_mod_cast hpos
    · exfalso
      have hnn : (0 : ℤ) ≤ (Int.gcd (w 0) (w 1) : ℤ) := Int.natCast_nonneg _
      omega
  obtain ⟨g, hg0, hg1⟩ := IsCoprime.exists_SL2_col hcop 0
  refine ⟨g, ?_⟩
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

/-- **Primitive-column completion helper (general dim ≥ 2)**: Given a primitive
integer vector `w : Fin (n + 2) → ℤ` (any common integer divisor of all entries
is a unit), there exists `N ∈ SL(Fin (n + 2), ℤ)` whose first column equals `w`.
Proved by induction on `n`: base case via `sl_exists_col_of_primitive_fin_2`;
inductive step via `sl_bezout_reduce_dim` + `sl_extend_at_1` + degenerate-case
transvection, using `sl_dvd_of_mulVec_dvd` for primitivity transfer. -/
private lemma sl_exists_col_of_primitive : ∀ {n : ℕ} (w : Fin (n + 2) → ℤ)
    (_hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d),
    ∃ N : SpecialLinearGroup (Fin (n + 2)) ℤ, ∀ i, N.1 i 0 = w i
  | 0, w, hw => sl_exists_col_of_primitive_fin_2 w hw
  | n + 1, w, hw => by
    have h_has_ne : ∃ j : Fin (n + 3), w j ≠ 0 := by
      by_contra h_all_zero
      push_neg at h_all_zero
      have : IsUnit (2 : ℤ) := hw 2 (fun i ↦ by rw [h_all_zero i]; exact dvd_zero _)
      rw [Int.isUnit_iff] at this; omega
    obtain ⟨T, hT_ne⟩ : ∃ T : SpecialLinearGroup (Fin (n + 3)) ℤ,
        (T.1 *ᵥ w) 0 ≠ 0 ∨ (T.1 *ᵥ w) 1 ≠ 0 := by
      by_cases h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0
      · refine ⟨1, ?_⟩
        rcases h_ne with h0 | h1
        · left; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
        · right; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      · push_neg at h_ne
        obtain ⟨hw0, hw1⟩ := h_ne
        obtain ⟨j, hj_ne⟩ := h_has_ne
        have hj_ge : 2 ≤ j.val := by
          by_contra hlt
          push_neg at hlt
          have h_01 : j.val = 0 ∨ j.val = 1 := by omega
          rcases h_01 with h0 | h1
          · apply hj_ne
            have : j = 0 := Fin.ext h0
            rw [this]; exact hw0
          · apply hj_ne
            have : j = 1 := Fin.ext h1
            rw [this]; exact hw1
        have hj_ne_1 : (1 : Fin (n + 3)) ≠ j := by
          apply Fin.ne_of_val_ne; show 1 ≠ j.val; omega
        have h_det : (Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ)).det = 1 :=
          Matrix.det_transvection_of_ne (1 : Fin (n + 3)) j hj_ne_1 (1 : ℤ)
        refine ⟨⟨Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ), h_det⟩, ?_⟩
        right
        show (Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ) *ᵥ w) 1 ≠ 0
        simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
          Matrix.single_mulVec, Pi.add_apply, Function.update_self]
        rw [hw1]; simpa using hj_ne
    set w_ok := T.1 *ᵥ w with hw_ok_def
    have hw_ok_prim : ∀ d : ℤ, (∀ i, d ∣ w_ok i) → IsUnit d := fun d hd ↦
      hw d (sl_dvd_of_mulVec_dvd T w d hd)
    obtain ⟨E, hE0, hE1, hErest⟩ := sl_bezout_reduce_dim w_ok hT_ne
    let w' : Fin (n + 2) → ℤ := fun i ↦
      if i.val = 0 then (Int.gcd (w_ok 0) (w_ok 1) : ℤ)
      else w_ok ⟨i.val + 1, by omega⟩
    have hw'_0 : w' 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := by simp [w']
    have hw'_succ : ∀ i : Fin (n + 1), w' ⟨i.val + 1, by omega⟩ =
        w_ok ⟨i.val + 2, by omega⟩ := by
      intro i
      show (if ((⟨i.val + 1, by omega⟩ : Fin (n + 2)).val = 0) then _ else _) = _
      rw [if_neg (by show i.val + 1 ≠ 0; omega)]
    have hw'_prim : ∀ d : ℤ, (∀ i, d ∣ w' i) → IsUnit d := by
      intro d hd
      apply hw_ok_prim
      intro k
      by_cases hk0 : k.val = 0
      · rw [show k = (⟨0, by omega⟩ : Fin (n + 3)) from Fin.ext hk0]
        have h_d_dvd_gcd : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := hw'_0 ▸ hd 0
        exact h_d_dvd_gcd.trans (Int.gcd_dvd_left _ _)
      · by_cases hk1 : k.val = 1
        · rw [show k = (⟨1, by omega⟩ : Fin (n + 3)) from Fin.ext hk1]
          have h_d_dvd_gcd : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := hw'_0 ▸ hd 0
          exact h_d_dvd_gcd.trans (Int.gcd_dvd_right _ _)
        · have h_ge : 2 ≤ k.val := by omega
          have h_lt : k.val < n + 3 := k.isLt
          let k' : Fin (n + 1) := ⟨k.val - 2, by omega⟩
          rw [show k = ⟨k'.val + 2, by omega⟩ from
            Fin.ext (by show k.val = k.val - 2 + 2; omega)]
          rw [← hw'_succ k']
          exact hd ⟨k'.val + 1, by omega⟩
    obtain ⟨N', hN'⟩ := sl_exists_col_of_primitive w' hw'_prim
    refine ⟨T⁻¹ * (E⁻¹ * sl_extend_at_1 N'), ?_⟩
    intro i
    have h_col0_eq : ∀ (j : Fin (n + 3)),
        (sl_extend_at_1 N').1 j 0 = (E.1 *ᵥ w_ok) j :=
      sl_extend_at_1_col_0_matches_reduce w_ok w' N' hN' hw'_0 hw'_succ E hE0 hE1 hErest
    have h_inv_mul_E : E⁻¹.1 * E.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_inv_mul_T : T⁻¹.1 * T.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_col_inner : (sl_extend_at_1 N').1 *ᵥ (Pi.single 0 (1 : ℤ)) = E.1 *ᵥ w_ok := by
      funext k
      rw [Matrix.mulVec_single_one]
      exact h_col0_eq k
    have h_N_col0 : (T⁻¹ * (E⁻¹ * sl_extend_at_1 N')).1 *ᵥ (Pi.single 0 (1 : ℤ)) = w := by
      show (T⁻¹.1 * (E⁻¹.1 * (sl_extend_at_1 N').1)) *ᵥ (Pi.single 0 (1 : ℤ)) = w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_col_inner]
      have h_E_cancel : E⁻¹.1 *ᵥ (E.1 *ᵥ w_ok) = w_ok := by
        rw [Matrix.mulVec_mulVec, h_inv_mul_E, Matrix.one_mulVec]
      rw [h_E_cancel]
      show T⁻¹.1 *ᵥ w_ok = w
      rw [hw_ok_def, Matrix.mulVec_mulVec, h_inv_mul_T, Matrix.one_mulVec]
    have := congr_fun h_N_col0 i
    rw [Matrix.mulVec_single_one] at this
    exact this


/-- **Fiber ⟹ mem_H bridge.** The dim-`k+2` set-form fiber condition on
`(i.out, j.out)` with `diagMat_delta` entries rewrites to the `diagMat`-shaped
H-membership condition consumed by `slSuccEmbed_H_fiber_transfer`-family
lemmas and by `hfib_col_div_a/b`. -/
private lemma hfib_to_mem_H {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
      (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) ∈
        (GL_pair (k + 2)).H := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  simp only [diagMat_delta_val (k + 2) (Fin.cons 1 a) hcons_a,
      diagMat_delta_val (k + 2) (Fin.cons 1 b) hcons_b,
      diagMat_delta_val (k + 2) (Fin.cons 1 c) hcons_c] at hfib
  exact (fiber_diagMat_iff_mem_H (Fin.cons 1 a) (Fin.cons 1 b) (Fin.cons 1 c)
    hcons_a hcons_b hcons_c i.out j.out).mp hfib

/-- **GL-level integer-conjugate identity (T193 bridge).**
Lifts the integer-matrix identity `D_a · N_i.val = M_i.val · D_a` (as produced by
`exists_stab_with_block_form_of_X_fiber`'s `h_int_conj` output) to the GL ℚ
form `D_a_GL · mapGL N_i = mapGL M_i · D_a_GL` required by the T192 helper
`jout_conj_N_i_stab_of_iMi_c_stab`. The lift is mechanical via
`Matrix.map (algebraMap ℤ ℚ)`. -/
private lemma h_int_conj_GL_of_int_mat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) :
    diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  apply Units.ext
  show ((diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL _ ℚ)).val :
        Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) =
      ((mapGL ℚ M_i : GL _ ℚ) * diagMat (k + 2) (Fin.cons 1 a)).val
  simp only [Units.val_mul]
  have h_Da : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ).val : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_pos,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_N : ((mapGL ℚ N_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      N_i.val.map (algebraMap ℤ ℚ) := rfl
  have h_M : ((mapGL ℚ M_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      M_i.val.map (algebraMap ℤ ℚ) := rfl
  rw [h_Da, h_N, h_M]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (fun M : Matrix _ _ ℤ ↦ M.map (algebraMap ℤ ℚ)) h_int_conj

/-- **GL-level fiber equation from the fiber condition (T193 bridge).**
GL ℚ form of `hfib_int_mat_eq`: directly produces
`i.out · D_a · j.out · D_b = D_c · mapGL ν` in `GL (Fin (k+2)) ℚ`, the input
required by the T192 helper `jout_conj_N_i_stab_of_iMi_c_stab`. -/
private lemma hfib_GL_eq {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) =
        diagMat (k + 2) (Fin.cons 1 c) * (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  obtain ⟨ν, hν⟩ := hfib_to_mem_H a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  have h_eq : diagMat (k + 2) (Fin.cons 1 c) *
      (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) =
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) := by
    rw [hν]; group
  exact h_eq.symm

/-- **Integer matrix equation from the fiber condition**. The H-membership from
`hfib_to_mem_H` is witnessed by some `ν : SL_{k+2}(ℤ)`; because every factor on
both sides is the `Int.cast` image of an integer matrix, the equation descends
to the integer level:
`A · D_a · B · D_b = D_c · ν`, where `A := toSL i.out`, `B := toSL j.out` and
`D_x := Matrix.diagonal (Fin.cons 1 x)` (entries cast to `ℤ`). This is the
clean integer handle used by the divisibility extraction lemmas. -/
private lemma hfib_int_mat_eq {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (toSL i.out).1 *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (toSL j.out).1 *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.1 := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have h_mem := hfib_to_mem_H a b c ha hb hc i j hfib
  obtain ⟨ν, hν⟩ := h_mem
  refine ⟨ν, ?_⟩
  have hmul : diagMat (k + 2) (Fin.cons 1 c) *
      (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) =
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) := by
    rw [hν]; group
  have hmat := congr_arg
    (fun g : GL (Fin (k + 2)) ℚ ↦ (g : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)) hmul
  simp only [Units.val_mul] at hmat
  have h_i : ((i.out : GL (Fin (k + 2)) ℚ) : Matrix _ _ ℚ) =
      (toSL i.out).1.map (algebraMap ℤ ℚ) := by
    rw [← toSL_spec i.out]; rfl
  have h_j : ((j.out : GL (Fin (k + 2)) ℚ) : Matrix _ _ ℚ) =
      (toSL j.out).1.map (algebraMap ℤ ℚ) := by
    rw [← toSL_spec j.out]; rfl
  have h_ν : ((mapGL ℚ ν : GL _ ℚ) : Matrix _ _ ℚ) = ν.1.map (algebraMap ℤ ℚ) := rfl
  have h_Da : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_a,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Db : ((diagMat (k + 2) (Fin.cons 1 b) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_b,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Dc : ((diagMat (k + 2) (Fin.cons 1 c) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_c,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [h_i, h_j, h_ν, h_Da, h_Db, h_Dc] at hmat
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul] at hmat
  exact (Matrix.map_injective (algebraMap ℤ ℚ).injective_int hmat).symm

/-- **Column-zero divisibility for `(toSL i.out)⁻¹`**. From the integer matrix
equation `A · D_a · B · D_b = D_c · ν` supplied by `hfib_int_mat_eq`, the entry
`((toSL i.out)⁻¹).1 r.succ 0` is divisible by `a r` for every `r : Fin (k+1)`.
Proof strategy: premultiply the equation by `adjugate A` and postmultiply by
`adjugate ν`, apply to `Pi.single 0 (1 : ℤ)` via `mulVec`, and read off the
diagonal entry. -/
private lemma hfib_col_div_a {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∀ r : Fin (k + 1),
      (a r : ℤ) ∣ ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  set A_i := (toSL i.out).1 with hA_i
  set A_j := (toSL j.out).1 with hA_j
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c
  have hdetA : A_i.det = 1 := (toSL i.out).2
  have hdetν : ν.1.det = 1 := ν.2
  have h_rearr : D_a * A_j * D_b * Matrix.adjugate ν.1 =
      Matrix.adjugate A_i * D_c := by
    have h1 : Matrix.adjugate A_i * (A_i * D_a * A_j * D_b) * Matrix.adjugate ν.1 =
        Matrix.adjugate A_i * (D_c * ν.1) * Matrix.adjugate ν.1 := by
      rw [hν]
    have hAA : Matrix.adjugate A_i * A_i = 1 := by
      rw [Matrix.adjugate_mul, hdetA, one_smul]
    have hνν : ν.1 * Matrix.adjugate ν.1 = 1 := by
      rw [Matrix.mul_adjugate, hdetν, one_smul]
    rw [show Matrix.adjugate A_i * (A_i * D_a * A_j * D_b) * Matrix.adjugate ν.1 =
            (Matrix.adjugate A_i * A_i) * D_a * A_j * D_b * Matrix.adjugate ν.1 by
          simp only [← Matrix.mul_assoc]] at h1
    rw [hAA, Matrix.one_mul] at h1
    rw [show Matrix.adjugate A_i * (D_c * ν.1) * Matrix.adjugate ν.1 =
            Matrix.adjugate A_i * D_c * (ν.1 * Matrix.adjugate ν.1) by
          simp only [← Matrix.mul_assoc]] at h1
    rw [hνν, Matrix.mul_one] at h1
    exact h1
  intro r
  have h_mul : ((D_a * A_j * D_b * Matrix.adjugate ν.1).mulVec (Pi.single 0 (1 : ℤ))) r.succ =
      ((Matrix.adjugate A_i * D_c).mulVec (Pi.single 0 (1 : ℤ))) r.succ := by
    rw [h_rearr]
  have hDc_mulVec : D_c.mulVec (Pi.single 0 (1 : ℤ)) = Pi.single 0 (1 : ℤ) := by
    rw [hD_c, Matrix.diagonal_mulVec_single]
    simp [Fin.cons_zero]
  have hRHS : ((Matrix.adjugate A_i * D_c).mulVec (Pi.single 0 (1 : ℤ))) r.succ =
      Matrix.adjugate A_i r.succ 0 := by
    rw [← Matrix.mulVec_mulVec, hDc_mulVec, Matrix.mulVec_single_one]
    rfl
  have hLHS : ((D_a * A_j * D_b * Matrix.adjugate ν.1).mulVec
      (Pi.single 0 (1 : ℤ))) r.succ =
      (a r : ℤ) *
        (((A_j * D_b * Matrix.adjugate ν.1).mulVec (Pi.single 0 (1 : ℤ))) r.succ) := by
    have hassoc : D_a * A_j * D_b * Matrix.adjugate ν.1 =
        D_a * (A_j * D_b * Matrix.adjugate ν.1) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc, ← Matrix.mulVec_mulVec]
    rw [hD_a, Matrix.mulVec_diagonal]
    simp [Fin.cons_succ]
  refine ⟨((A_j * D_b * Matrix.adjugate ν.1).mulVec (Pi.single 0 (1 : ℤ))) r.succ, ?_⟩
  rw [hLHS, hRHS] at h_mul
  have : ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 =
      Matrix.adjugate A_i r.succ 0 := by
    rw [SpecialLinearGroup.coe_inv]
  rw [this, ← h_mul]

/-- **Row-zero divisibility for `ν` (T001 Layer 1 precursor).** From the integer
matrix equation `A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`), the
entry `ν_{0, r.succ}` is divisible by `b r` for every `r : Fin (k+1)`.

**Derivation.** Look at row 0, column `r.succ` of both sides. With `(D_c)_{0, 0}
= 1` and `(D_b)_{r.succ, r.succ} = b r`, row 0 col `r.succ` of `D_c · ν` equals
`ν_{0, r.succ}`, while row 0 col `r.succ` of `A_i · D_a · A_j · D_b` carries an
explicit `b r` factor (the right-multiplication by `D_b` scales col `r.succ`
by `b r`).

**Use site (T001 Layer 1 reduction).** This is the single direct divisibility
constraint extracted from the fiber equation that survives the structural
asymmetry obstruction documented at `hfib_col_div_b_canonical_stmt`.  It is
strictly weaker than `hfib_col_div_b_canonical_stmt` (which asks for
divisibility on `(toSL j.out)⁻¹` = `adj A_j`), but is provable in Lean and
isolates the next step needed: a lattice-descent / cofactor argument bridging
`b r ∣ ν_{0, r.succ}` to `b r ∣ adj(A_j)_{r.succ, 0}` via the SL determinant
constraint on `ν` and the structure of the equation. -/
private lemma hfib_row_div_b_nu_top_row {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∀ r : Fin (k + 1),
      ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (b r : ℤ) ∣ ν.1 0 r.succ := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  refine fun r ↦ ⟨ν, ?_⟩
  have h_entry : ((toSL i.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
      (toSL j.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) 0 r.succ =
      (Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) * ν.1) 0 r.succ :=
    congr_fun (congr_fun hν 0) r.succ
  have h_RHS : (Matrix.diagonal (fun s : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) * ν.1) 0 r.succ =
      ν.1 0 r.succ := by
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_apply]
    simp [Fin.cons_zero]
  have h_LHS : ((toSL i.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
      (toSL j.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) 0 r.succ =
      (b r : ℤ) *
        ((toSL i.out).1 *
          Matrix.diagonal (fun s : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
          (toSL j.out).1) 0 r.succ := by
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_apply]
    simp [Fin.cons_succ, mul_comm]
  rw [h_LHS, h_RHS] at h_entry
  exact ⟨_, h_entry.symm⟩

/-- **SL elementary column op**: right-multiplication by `slTransvecG i j hij c`
adds `c` times column `i` to column `j` and leaves all other columns unchanged.
Specialised entry formula: at column `j`, the new entry is the original `(a, j)`
plus `c` times the original `(a, i)`. This is the unbundled form used by the
column-by-column Bezout reduction. -/
private lemma sl_addCol_target_col {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (c : ℤ) (M : SpecialLinearGroup (Fin m) ℤ) (a : Fin m) :
    (M * slTransvecG i j hij c).1 a j = M.1 a j + c * M.1 a i := by
  have hcoe : (M * slTransvecG i j hij c).1 = M.1 * Matrix.transvection i j c := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  simp [Matrix.transvection, Matrix.mul_add, mul_comm]

/-- **SL elementary column op preserves untouched columns**: at any column
`k ≠ j`, the entry is unchanged. -/
private lemma sl_addCol_preserves_col {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (c : ℤ) (M : SpecialLinearGroup (Fin m) ℤ) (a : Fin m) {k : Fin m} (hk : k ≠ j) :
    (M * slTransvecG i j hij c).1 a k = M.1 a k := by
  have hcoe : (M * slTransvecG i j hij c).1 = M.1 * Matrix.transvection i j c := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  simp [Matrix.transvection, Matrix.mul_add, hk]

/-- **Multi-transvection column accumulation (Finset version).** Iterating a
family of transvections `slTransvecG k k₀ (h_ne k) (c k)` over `k ∈ S` (where
`S` avoids `k₀`) right-multiplies `N` by some `U ∈ SL` whose net effect adds
`∑ k ∈ S, c k * (column k)` to column `k₀` and leaves all columns `k ≠ k₀`
unchanged. Crucially, the donor columns `k ∈ S` are not modified during the
process (each transvection touches only column `k₀`), so the cumulative sum is
the original sum, not a telescoped one. -/
private lemma sl_addCol_finset_target_aux {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (k₀ : Fin n.succ) (c : Fin n.succ → ℤ)
    (S : Finset (Fin n.succ)) (hS : k₀ ∉ S) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      (∀ a, (N * U).1 a k₀ = N.1 a k₀ + ∑ k ∈ S, c k * N.1 a k) := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_⟩
      · intro a k _; simp
      · intro a; simp
  | insert k T hkT ih =>
      have hk_ne_k₀ : k ≠ k₀ := by
        intro h; apply hS; rw [h]; exact Finset.mem_insert_self _ _
      have hT_no_k₀ : k₀ ∉ T :=
        fun h ↦ hS (Finset.mem_insert_of_mem h)
      obtain ⟨U, hU_pres, hU_target⟩ := ih hT_no_k₀
      refine ⟨U * slTransvecG k k₀ hk_ne_k₀ (c k), ?_, ?_⟩
      · intro a k' hk'
        rw [← mul_assoc, sl_addCol_preserves_col k k₀ hk_ne_k₀ (c k) (N * U) a hk']
        exact hU_pres a k' hk'
      · intro a
        rw [← mul_assoc, sl_addCol_target_col k k₀ hk_ne_k₀ (c k) (N * U) a]
        rw [hU_target a, hU_pres a k hk_ne_k₀]
        rw [Finset.sum_insert hkT]
        ring

/-- **Multi-transvection column accumulation, full sum form.** Specialisation
of `sl_addCol_finset_target_aux` to `S = Finset.univ.erase k₀`: when the
coefficient at the target column `c k₀ = 0`, the cumulative effect is the
full sum `∑ k, c k * N.1 a k` (since the `k = k₀` term contributes zero). -/
private lemma sl_addCol_finset_target {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (k₀ : Fin n.succ) (c : Fin n.succ → ℤ) (h_zero : c k₀ = 0) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      (∀ a, (N * U).1 a k₀ = N.1 a k₀ + ∑ k, c k * N.1 a k) := by
  have hS : k₀ ∉ Finset.univ.erase k₀ := Finset.notMem_erase _ _
  obtain ⟨U, hU_pres, hU_target⟩ :=
    sl_addCol_finset_target_aux N k₀ c (Finset.univ.erase k₀) hS
  refine ⟨U, hU_pres, ?_⟩
  intro a
  rw [hU_target a]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k₀)]
  rw [h_zero, zero_mul, add_zero]

/-- **One-row modular clearance.** If the row-`r` entries of `N`, with column
`k₀` excluded, already generate the unit ideal (`h_redundant`), then for any
modulus `m` there is a single SL elementary product `U` (composition of
transvections with donors `k ≠ k₀`) such that `m ∣ (N * U).1 r k₀` and all
columns `k ≠ k₀` are preserved. Combines `sl_row_clear_mod_avoiding`
(produces Bezout coefficients `c` with `c k₀ = 0` and
`m ∣ N.1 r k₀ + ∑ c k * N.1 r k`) with `sl_addCol_finset_target` (realises
the cumulative column-effect as a product of transvections). -/
private lemma sl_clear_row_modular {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (k₀ : Fin n.succ) (m : ℤ)
    (h_redundant : ∃ c₀ : Fin n.succ → ℤ,
      c₀ k₀ = 0 ∧ ∑ k, c₀ k * N.1 r k = 1) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      m ∣ (N * U).1 r k₀ := by
  obtain ⟨c, hc_zero, hc_dvd⟩ :=
    sl_row_clear_mod_avoiding N r k₀ h_redundant (N.1 r k₀) m
  obtain ⟨U, hU_pres, hU_target⟩ := sl_addCol_finset_target N k₀ c hc_zero
  refine ⟨U, hU_pres, ?_⟩
  rw [hU_target r]
  exact hc_dvd

/-- **Bezout column reduction**: given a matrix `M` and two distinct columns
`i ≠ j`, with `M_{r, i}` non-zero (or jointly with `M_{r, j}`), there exists
a determinant-1 elementary column operation (right-multiplication by an SL
transvection) modifying only column `j` so that the entry `M_{r, j}` is
reduced modulo `M_{r, i}`. Concretely: choose `c = -(M_{r, j} / M_{r, i})`,
giving new `(r, j)`-entry equal to `M_{r, j} % M_{r, i}` (the Euclidean
remainder). All other columns are unchanged.

This is the primitive column-op step used in the column-by-column Smith
reduction toward the DivChain stabilizer form. -/
private lemma sl_addCol_emod_step {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r : Fin m) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (M * U).1 r j = M.1 r j % M.1 r i := by
  refine ⟨slTransvecG i j hij (-(M.1 r j / M.1 r i)), ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r]
    have := Int.emod_def (M.1 r j) (M.1 r i)
    linarith [this]

/-- **Bezout column reduction making `d` divide the entry**: given a matrix
`M`, two distinct columns `i ≠ j`, a row `r`, and a divisor `d`, if the pivot
`M.1 r i` is coprime to `d`, there is an SL transvection adding a multiple of
column `i` to column `j` so that `d ∣ (M * U).1 r j`. All columns `k ≠ j` are
preserved. -/
private lemma sl_addCol_make_dvd {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r : Fin m) (d : ℤ)
    (h_cop : IsCoprime (M.1 r i) d) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      d ∣ (M * U).1 r j := by
  obtain ⟨s, t, hst⟩ := h_cop
  refine ⟨slTransvecG i j hij (-(M.1 r j) * s), ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r]
    refine ⟨M.1 r j * t, ?_⟩
    have : M.1 r j * (s * M.1 r i + t * d) = M.1 r j * 1 := by rw [hst]
    linarith [this]

/-- **Two-row simultaneous Bezout column reduction (CRT case)**: given a
matrix `M`, two distinct columns `i ≠ j`, two distinct rows `r₁ ≠ r₂`, and two
divisors `d₁, d₂` with `IsCoprime d₁ d₂`, if the pivot entries `M.1 r₁ i` and
`M.1 r₂ i` are coprime to their respective divisors, there is a single SL
transvection adding a multiple of column `i` to column `j` so that
`d₁ ∣ (M * U).1 r₁ j` AND `d₂ ∣ (M * U).1 r₂ j`. All columns `k ≠ j` are
preserved.

The construction is an explicit CRT lift of the per-row Bezout coefficients:
from `s₁·M.1 r₁ i + t₁·d₁ = 1` and `s₂·M.1 r₂ i + t₂·d₂ = 1` and
`u·d₁ + v·d₂ = 1`, set `c₁ := -M.1 r₁ j · s₁`, `c₂ := -M.1 r₂ j · s₂`, and
`c := v·d₂·c₁ + u·d₁·c₂`. Then `c ≡ c₁ [MOD d₁]` and `c ≡ c₂ [MOD d₂]`,
solving both congruences simultaneously. -/
private lemma sl_addCol_make_dvd_two_coprime {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r₁ r₂ : Fin m) (d₁ d₂ : ℤ)
    (h_cop₁ : IsCoprime (M.1 r₁ i) d₁) (h_cop₂ : IsCoprime (M.1 r₂ i) d₂)
    (h_cop_d : IsCoprime d₁ d₂) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (d₁ ∣ (M * U).1 r₁ j) ∧ (d₂ ∣ (M * U).1 r₂ j) := by
  obtain ⟨s₁, t₁, hst₁⟩ := h_cop₁
  obtain ⟨s₂, t₂, hst₂⟩ := h_cop₂
  obtain ⟨u, v, huv⟩ := h_cop_d
  set c₁ : ℤ := -(M.1 r₁ j) * s₁ with hc₁_def
  set c₂ : ℤ := -(M.1 r₂ j) * s₂ with hc₂_def
  set c : ℤ := v * d₂ * c₁ + u * d₁ * c₂ with hc_def
  refine ⟨slTransvecG i j hij c, ?_, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · -- Show d₁ ∣ M.1 r₁ j + c * M.1 r₁ i.
    rw [sl_addCol_target_col i j hij _ M r₁]
    refine ⟨M.1 r₁ j * t₁ + (u * c₂ - u * c₁) * M.1 r₁ i, ?_⟩
    have key : M.1 r₁ j * (s₁ * M.1 r₁ i + t₁ * d₁) = M.1 r₁ j * 1 := by rw [hst₁]
    have hvd₂ : v * d₂ = 1 - u * d₁ := by linarith [huv]
    have : M.1 r₁ j + c * M.1 r₁ i =
        (M.1 r₁ j + c₁ * M.1 r₁ i) + (c - c₁) * M.1 r₁ i := by ring
    rw [this]
    have hc_diff : c - c₁ = d₁ * (u * c₂ - u * c₁) := by
      rw [hc_def]
      have : v * d₂ * c₁ + u * d₁ * c₂ - c₁ =
          (v * d₂ - 1) * c₁ + u * d₁ * c₂ := by ring
      rw [this, hvd₂]
      ring
    rw [hc_diff]
    have hfirst : M.1 r₁ j + c₁ * M.1 r₁ i = d₁ * (M.1 r₁ j * t₁) := by
      rw [hc₁_def]
      linarith [key]
    rw [hfirst]
    ring
  · -- Symmetric argument with d₂.
    rw [sl_addCol_target_col i j hij _ M r₂]
    refine ⟨M.1 r₂ j * t₂ + (v * c₁ - v * c₂) * M.1 r₂ i, ?_⟩
    have key : M.1 r₂ j * (s₂ * M.1 r₂ i + t₂ * d₂) = M.1 r₂ j * 1 := by rw [hst₂]
    have hud₁ : u * d₁ = 1 - v * d₂ := by linarith [huv]
    have : M.1 r₂ j + c * M.1 r₂ i =
        (M.1 r₂ j + c₂ * M.1 r₂ i) + (c - c₂) * M.1 r₂ i := by ring
    rw [this]
    have hc_diff : c - c₂ = d₂ * (v * c₁ - v * c₂) := by
      rw [hc_def]
      have : v * d₂ * c₁ + u * d₁ * c₂ - c₂ =
          v * d₂ * c₁ + (u * d₁ - 1) * c₂ := by ring
      rw [this, hud₁]
      ring
    rw [hc_diff]
    have hfirst : M.1 r₂ j + c₂ * M.1 r₂ i = d₂ * (M.1 r₂ j * t₂) := by
      rw [hc₂_def]
      linarith [key]
    rw [hfirst]
    ring

/-- **Two-row simultaneous Bezout column reduction (CRT compatibility case)**:
NOT requiring pairwise-coprime divisors. Given pre-supplied per-row Bezout
residues `c₁, c₂` with `d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i` and
`d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i`, plus the CRT compatibility
`(Int.gcd d₁ d₂ : ℤ) ∣ c₁ - c₂`, there is an SL transvection adding a multiple
of column `i` to column `j` so that simultaneously
`d₁ ∣ (M * U).1 r₁ j` and `d₂ ∣ (M * U).1 r₂ j`. All columns `k ≠ j` are
preserved.

The construction takes the unified coefficient `c := c₁ - u * d₁ * δ` where
`u := Int.gcdA d₁ d₂`, `v := Int.gcdB d₁ d₂`, `g := (Int.gcd d₁ d₂ : ℤ)`, and
`δ` is the witness `c₁ - c₂ = g * δ`. Then
`c - c₁ = -u * d₁ * δ` (divisible by `d₁`) and `c - c₂ = v * d₂ * δ`
(divisible by `d₂`), giving the simultaneous solution.

This generalises `sl_addCol_make_dvd_two_coprime`: when `IsCoprime d₁ d₂`, the
gcd is a unit so the compatibility hypothesis is trivial. The natural use case
is a divisibility-chain `d₁ ∣ d₂` (then `Int.gcd d₁ d₂ = |d₁|` divides any
multiple, in particular `c₁ - c₂` whenever the system is consistent). -/
private lemma sl_addCol_make_dvd_two_compat {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r₁ r₂ : Fin m) (d₁ d₂ : ℤ)
    (c₁ c₂ : ℤ)
    (h₁ : d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i)
    (h₂ : d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i)
    (h_compat : (Int.gcd d₁ d₂ : ℤ) ∣ c₁ - c₂) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (d₁ ∣ (M * U).1 r₁ j) ∧ (d₂ ∣ (M * U).1 r₂ j) := by
  set u : ℤ := Int.gcdA d₁ d₂ with hu_def
  set v : ℤ := Int.gcdB d₁ d₂ with hv_def
  have hbezout : (Int.gcd d₁ d₂ : ℤ) = d₁ * u + d₂ * v := Int.gcd_eq_gcd_ab d₁ d₂
  obtain ⟨δ, hδ⟩ := h_compat
  set c : ℤ := c₁ - u * d₁ * δ with hc_def
  refine ⟨slTransvecG i j hij c, ?_, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · -- Show d₁ ∣ M.1 r₁ j + c * M.1 r₁ i.
    rw [sl_addCol_target_col i j hij _ M r₁]
    have hsplit : M.1 r₁ j + c * M.1 r₁ i =
        (M.1 r₁ j + c₁ * M.1 r₁ i) + (c - c₁) * M.1 r₁ i := by ring
    rw [hsplit]
    have hcc₁ : c - c₁ = -(u * d₁ * δ) := by rw [hc_def]; ring
    have hd₁_dvd_second : d₁ ∣ (c - c₁) * M.1 r₁ i := by
      rw [hcc₁]
      refine Dvd.dvd.mul_right ?_ _
      refine (dvd_neg).mpr ?_
      exact ⟨u * δ, by ring⟩
    exact dvd_add h₁ hd₁_dvd_second
  · -- Show d₂ ∣ M.1 r₂ j + c * M.1 r₂ i.
    rw [sl_addCol_target_col i j hij _ M r₂]
    have hsplit : M.1 r₂ j + c * M.1 r₂ i =
        (M.1 r₂ j + c₂ * M.1 r₂ i) + (c - c₂) * M.1 r₂ i := by ring
    rw [hsplit]
    have hcc₂ : c - c₂ = v * d₂ * δ := by
      have hkey : c - c₂ = (c₁ - c₂) - u * d₁ * δ := by rw [hc_def]; ring
      rw [hkey, hδ, hbezout]
      ring
    have hd₂_dvd_second : d₂ ∣ (c - c₂) * M.1 r₂ i := by
      rw [hcc₂]
      exact ⟨v * δ * M.1 r₂ i, by ring⟩
    exact dvd_add h₂ hd₂_dvd_second

/-- **Finite-row simultaneous Bezout column reduction (CRT wrapper)**: given a
matrix `M`, two distinct columns `i ≠ j`, a finite set of rows `R` with a
divisor `d r` for each `r ∈ R` such that the pivots `M.1 r i` are coprime to
`d r` and the divisors are pairwise coprime, there is a single SL matrix
(product of transvections in column `j`, leaving every column `k ≠ j`
unchanged) so that `d r ∣ (M * U).1 r j` for every `r ∈ R`.

The proof is by induction on `R`: at each step we adjoin a transvection whose
coefficient is a multiple of the running product `∏_{r ∈ R} d r` (so previous
divisibilities are preserved) and that solves the new Bezout congruence for
the inserted row (using coprimality between `M.1 r₀ i · D` and `d r₀`). -/
private lemma sl_addCol_make_dvd_finset
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ)
    (h_cop : ∀ r ∈ R, IsCoprime (M.1 r i) (d r))
    (h_pairwise : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → IsCoprime (d r₁) (d r₂)) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_⟩
      · intro a k _; simp
      · intro r hr; exact absurd hr (Finset.notMem_empty r)
  | insert r₀ R hr₀ IH =>
      have h_cop_R : ∀ r ∈ R, IsCoprime (M.1 r i) (d r) := fun r hr ↦
        h_cop r (Finset.mem_insert_of_mem hr)
      have h_pairwise_R : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → IsCoprime (d r₁) (d r₂) :=
        fun r₁ hr₁ r₂ hr₂ hne ↦
          h_pairwise r₁ (Finset.mem_insert_of_mem hr₁) r₂
            (Finset.mem_insert_of_mem hr₂) hne
      obtain ⟨U_R, hU_R_pres, hU_R_div⟩ := IH h_cop_R h_pairwise_R
      have h_cop_prod : IsCoprime (∏ r ∈ R, d r) (d r₀) := by
        refine (IsCoprime.prod_right (fun r hr ↦ ?_)).symm
        have hr_ne : r₀ ≠ r := by
          intro h; exact hr₀ (h ▸ hr)
        exact h_pairwise r₀ (Finset.mem_insert_self _ _) r
          (Finset.mem_insert_of_mem hr) hr_ne
      have h_cop_r₀ : IsCoprime (M.1 r₀ i) (d r₀) :=
        h_cop r₀ (Finset.mem_insert_self _ _)
      have h_cop_combined :
          IsCoprime ((∏ r ∈ R, d r) * M.1 r₀ i) (d r₀) :=
        h_cop_prod.mul_left h_cop_r₀
      obtain ⟨s, t, hst⟩ := h_cop_combined
      set D : ℤ := ∏ r ∈ R, d r with hD_def
      set v : ℤ := -((M * U_R).1 r₀ j) * s with hv_def
      set c' : ℤ := D * v with hc'_def
      refine ⟨U_R * slTransvecG i j hij c', ?_, ?_⟩
      · -- Preserve every column `k ≠ j`.
        intro a k hk
        rw [← mul_assoc]
        rw [sl_addCol_preserves_col i j hij c' (M * U_R) a hk]
        exact hU_R_pres a k hk
      · intro r hr
        rcases Finset.mem_insert.mp hr with hr_eq | hr_mem
        · -- Case r = r₀: divisibility from the chosen `c'`.
          subst hr_eq
          rw [← mul_assoc, sl_addCol_target_col i j hij c' (M * U_R) r]
          rw [hU_R_pres r i hij]
          refine ⟨(M * U_R).1 r j * t, ?_⟩
          have hkey : (M * U_R).1 r j *
              (s * (D * M.1 r i) + t * d r) = (M * U_R).1 r j * 1 := by
            rw [hst]
          have hexpand : (M * U_R).1 r j +
              c' * M.1 r i = d r * ((M * U_R).1 r j * t) := by
            have hv_expand : c' * M.1 r i = (M * U_R).1 r j *
                (s * (D * M.1 r i)) * (-1) := by
              rw [hc'_def, hv_def]; ring
            have hkey' : (M * U_R).1 r j * (s * (D * M.1 r i)) +
                (M * U_R).1 r j * (t * d r) = (M * U_R).1 r j := by
              have := hkey
              linarith
            linarith [hkey']
          linarith [hexpand]
        · -- Case r ∈ R: previous divisibility preserved because
          rw [← mul_assoc, sl_addCol_target_col i j hij c' (M * U_R) r]
          rw [hU_R_pres r i hij]
          have h_dr_div_D : d r ∣ D := by
            rw [hD_def]
            exact Finset.dvd_prod_of_mem d hr_mem
          have h_dr_div_c' : d r ∣ c' := by
            rw [hc'_def]; exact Dvd.dvd.mul_right h_dr_div_D _
          have h_div_first : d r ∣ (M * U_R).1 r j := hU_R_div r hr_mem
          exact dvd_add h_div_first (h_dr_div_c'.mul_right _)

/-- **Common-residue finite-row CRT wrapper.** When a SINGLE coefficient `c`
already simultaneously solves the divisibility `d r ∣ M.1 r j + c * M.1 r i`
for every row `r ∈ R`, a single transvection `slTransvecG i j hij c` suffices
to land all rows. This is the trivial pre-aligned case, useful when the
caller has already produced a common Bezout coefficient. -/
private lemma sl_addCol_make_dvd_common
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ) (c : ℤ)
    (h_dvd : ∀ r ∈ R, d r ∣ M.1 r j + c * M.1 r i) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  refine ⟨slTransvecG i j hij c, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij c M a hk
  · intro r hr
    rw [sl_addCol_target_col i j hij c M r]
    exact h_dvd r hr

/-- **Chain-compatible finite-row CRT wrapper.** Given per-row residues `c r`
solving `d r ∣ M.1 r j + c r * M.1 r i`, plus a "top element" `r_top ∈ R`
whose modulus `d r_top` is divisible by every `d r` (`r ∈ R`), and a chain
compatibility `d r ∣ c r_top - c r` for all `r ∈ R`, a single transvection
with coefficient `c r_top` lands all rows simultaneously. The compatibility
hypothesis is the precise content of "the per-row residues agree mod the
smaller moduli of the chain". -/
private lemma sl_addCol_make_dvd_chain_top
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ) (c : Fin m → ℤ)
    (h_dvd : ∀ r ∈ R, d r ∣ M.1 r j + c r * M.1 r i)
    {r_top : Fin m} (_ : r_top ∈ R)
    (_ : ∀ r ∈ R, d r ∣ d r_top)
    (h_chain : ∀ r ∈ R, d r ∣ c r_top - c r) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  refine sl_addCol_make_dvd_common i j hij M R d (c r_top) ?_
  intro r hr
  have h_diff : d r ∣ (c r_top - c r) * M.1 r i :=
    Dvd.dvd.mul_right (h_chain r hr) _
  have h_sum : d r ∣ (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i :=
    dvd_add (h_dvd r hr) h_diff
  have h_eq :
      (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i
        = M.1 r j + c r_top * M.1 r i := by ring
  rw [h_eq] at h_sum
  exact h_sum

/-- **Lower-clearance reduction.** If we already have an `N ∈ SL_{k+2}(ℤ)` with
the desired first column `w` and whose strictly-lower-triangular entries
`N i.succ j.succ` (for `j < i`) satisfy the `a i / a j` divisibility, then `N`
already lies in the diag-conjugation stabilizer. This packages the entry-wise
divisibility check via `diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd`. -/
private lemma sl_exists_col_stab_divChain_of_lower_clearance {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_lower : ∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N' : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  refine ⟨N, hcol, ?_⟩
  apply diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd a ha N
  intro i j
  refine Fin.cases ?_ ?_ i
  · -- i = 0: LHS = 1
    simp
  · intro i'
    refine Fin.cases ?_ ?_ j
    · -- j = 0, i = i'.succ
      simp only [Fin.cons_succ, Fin.cons_zero, Nat.cast_one, mul_one]
      have hcol_i := hcol i'.succ
      rw [hcol_i]
      exact hw_col_div i'
    · intro j'
      simp only [Fin.cons_succ]
      by_cases hij : j' < i'
      · -- Use h_lower i' j' hij
        have hdvd_q : ((a i' / a j' : ℕ) : ℤ) ∣ N.1 i'.succ j'.succ :=
          h_lower i' j' hij
        have hji_le : j' ≤ i' := le_of_lt hij
        have ha_dvd : a j' ∣ a i' := divChain_dvd (n := k + 1) hda hji_le
        have hmul : (((a i' / a j' : ℕ) : ℤ) * (a j' : ℤ)) ∣
            N.1 i'.succ j'.succ * (a j' : ℤ) :=
          mul_dvd_mul_right hdvd_q _
        have hcancel : (a i' / a j') * a j' = a i' :=
          Nat.div_mul_cancel ha_dvd
        have hcancel_int : ((a i' / a j' : ℕ) : ℤ) * (a j' : ℤ) = (a i' : ℤ) := by
          have := congr_arg (fun n : ℕ ↦ (n : ℤ)) hcancel
          push_cast at this
          exact this
        rw [hcancel_int] at hmul
        exact hmul
      · -- ¬ j' < i', i.e. i' ≤ j'.  Then a i' ∣ a j' by divChain.
        push_neg at hij
        have ha_dvd : a i' ∣ a j' := divChain_dvd (n := k + 1) hda hij
        have ha_dvd_int : (a i' : ℤ) ∣ (a j' : ℤ) := by exact_mod_cast ha_dvd
        exact Dvd.dvd.mul_left ha_dvd_int _

/-- **Donor-coprime + residue-aligned column clearance.** This is the precise
reduction of "clear column `j.succ` below row `j+1` against the DivChain
moduli `(a i / a j)` using donor column `i_don ≠ j.succ`" to the existence
of a SINGLE Bezout coefficient `c` that simultaneously aligns all the lower
rows. It is `sl_addCol_make_dvd_common` specialised to the row set
`{i.succ : i > j}` and the DivChain modulus pattern. The donor-coprime
hypothesis `h_don_ne` is consumed only to invoke the underlying transvection.
The caller is responsible for producing `c` and the joint residue
hypothesis `h_clear` (typically via Smith-style reduction or row-by-row
Bezout combined with chain compatibility). -/
private lemma sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : ℤ)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c * N.1 i.succ i_don)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  let R : Finset (Fin (k + 2)) :=
    (Finset.univ.filter (fun i : Fin (k + 1) ↦ j < i)).image Fin.succ
  let d : Fin (k + 2) → ℤ := fun r ↦
    Fin.cases (0 : ℤ) (fun i' ↦ if j < i' then ((a i' / a j : ℕ) : ℤ) else 0) r
  obtain ⟨U, hU_pres, hU_div⟩ :=
    sl_addCol_make_dvd_common (m := k + 2) i_don j.succ h_don_ne N R d c
      (by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨i, hi_mem, hi_eq⟩
        rcases Finset.mem_filter.mp hi_mem with ⟨_, hi_lt⟩
        subst hi_eq
        have hd_eq : d i.succ = ((a i / a j : ℕ) : ℤ) := by
          simp [d, Fin.cases_succ, hi_lt]
        rw [hd_eq]
        exact h_clear i hi_lt)
  refine ⟨U, hU_pres, ?_⟩
  intro i hi_lt
  have hi_mem : i.succ ∈ R := by
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_lt⟩
  have hd_eq : d i.succ = ((a i / a j : ℕ) : ℤ) := by
    simp [d, Fin.cases_succ, hi_lt]
  have := hU_div i.succ hi_mem
  rwa [hd_eq] at this

/-- **Compatible-residues wrapper** for column clearance. Packages the
solvability hypothesis as an existential, hiding the explicit Bezout
coefficient `c` from the caller. One-line reduction to
`sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue`. -/
private lemma sl_clear_one_column_lower_divChain_of_compatible_residues
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (h_solvable : ∃ c : ℤ, ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c * N.1 i.succ i_don)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  obtain ⟨c, h_clear⟩ := h_solvable
  exact sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    a ha hda j N i_don h_don_ne c h_clear

/-- **Pure-arithmetic CRT compatibility for chain moduli.** For a tower of
moduli `d : Fin n → ℤ` totally ordered by divisibility (`i ≤ j → d i ∣ d j`)
and per-row data `b, m : Fin n → ℤ`, the existence of a single coefficient
`c` simultaneously satisfying `d i ∣ c * m i + b i` for all rows `i` is
equivalent to the existence of per-row coefficients `c_per i` satisfying
each row, together with the chain compatibility `d i ∣ c_per j - c_per i`
whenever `i ≤ j`. The forward direction uses `c_per i := c` (and chain
compatibility is then trivial). The backward direction takes
`c := c_per ⟨n-1, _⟩` (or `0` when `n = 0`); the difference
`(c - c_per i) * m i` is divisible by `d i` exactly because of the chain
compatibility hypothesis. -/
private lemma exists_chain_solution_iff_compatible
    {n : ℕ} (d : Fin n → ℤ) (_h_chain : ∀ i j : Fin n, i ≤ j → d i ∣ d j)
    (b m : Fin n → ℤ) :
    (∃ c : ℤ, ∀ i : Fin n, d i ∣ c * m i + b i) ↔
      (∃ c_per : Fin n → ℤ,
        (∀ i : Fin n, d i ∣ c_per i * m i + b i) ∧
        (∀ i j : Fin n, i ≤ j → d i ∣ c_per j - c_per i)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun _ ↦ c, hc, ?_⟩
    intro i j _hij
    simp
  · rintro ⟨c_per, h_row, h_compat⟩
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- vacuous: no rows
      refine ⟨0, ?_⟩
      intro i
      exact absurd i.isLt (by simp [hn0])
    · -- take c := c_per (last)
      set last : Fin n := ⟨n - 1, by omega⟩
      refine ⟨c_per last, ?_⟩
      intro i
      have hi_le : i ≤ last := by
        refine Fin.mk_le_of_le_val ?_
        have : i.val ≤ n - 1 := by have := i.isLt; omega
        simpa using this
      have hcompat : d i ∣ c_per last - c_per i := h_compat i last hi_le
      have hdvd_diff : d i ∣ (c_per last - c_per i) * m i := hcompat.mul_right _
      have hsum := (h_row i).add hdvd_diff
      have heq : c_per i * m i + b i + (c_per last - c_per i) * m i =
          c_per last * m i + b i := by ring
      rw [heq] at hsum
      exact hsum

/-- **Chain-residues wrapper** for column clearance. Given per-row Bezout
coefficients `c i` and a chain-compatibility hypothesis (the residues
`c i'` and `c i` agree modulo `(a i / a j)` whenever `i ≤ i'`), we can
collapse to a single coefficient `c (Fin.last k)` that simultaneously
clears all rows. The chain compatibility is exactly the divisibility
needed to absorb the difference `(c (Fin.last) - c i) * N.1 i.succ i_don`
into the modulus. -/
private lemma sl_clear_one_column_lower_divChain_of_chain_residues
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : Fin (k + 1) → ℤ)
    (h_per_row : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don))
    (h_chain_compat : ∀ i i' : Fin (k + 1), j < i → i ≤ i' →
      (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  refine sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    a ha hda j N i_don h_don_ne (c (Fin.last k)) ?_
  intro i hi_lt
  have hrow := h_per_row i hi_lt
  have hcompat := h_chain_compat i (Fin.last k) hi_lt (Fin.le_last _)
  have hdiff : (((a i / a j : ℕ) : ℤ)) ∣
      (c (Fin.last k) - c i) * N.1 i.succ i_don :=
    hcompat.mul_right _
  have hsum := hrow.add hdiff
  have heq : N.1 i.succ j.succ + c i * N.1 i.succ i_don +
      (c (Fin.last k) - c i) * N.1 i.succ i_don =
      N.1 i.succ j.succ + c (Fin.last k) * N.1 i.succ i_don := by ring
  rw [heq] at hsum
  exact hsum

/-- **One-column induction step (first nonzero-donor completion).**

Given an `SL` matrix `N` with first column `w` and previously-cleared
columns `1, …, j` (lower-triangular `DivChain` divisibilities at each
column `j' ≤ j`, restricted to rows below the diagonal), together with
a donor column `i_don` distinct from the target column `j.succ` and
chain-compatible per-row residue data `c` for the target column,
produce `N'` with the same first column and with cleared columns
`1, …, j.succ`.

The proof composes `N` with the elementary clearance unit
`U` from `sl_clear_one_column_lower_divChain_of_chain_residues`.
Since `U` only modifies column `j.succ`, all columns `j'.succ` with
`j' ≤ j` are preserved (including column 0): for `j' < j` use
`(j'.succ ≠ j.succ)` from `Fin.succ_inj`, and for `j' = j` we
get the new clearance directly from the chain-residues output. -/
private lemma sl_clear_one_column_step
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
      (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ))
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : Fin (k + 1) → ℤ)
    (h_per_row : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don))
    (h_chain_compat : ∀ i i' : Fin (k + 1), j < i → i ≤ i' →
      (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) := by
  obtain ⟨U, hU_pres, hU_clear⟩ :=
    sl_clear_one_column_lower_divChain_of_chain_residues
      a ha hda j N i_don h_don_ne c h_per_row h_chain_compat
  refine ⟨N * U, ?_, ?_⟩
  · -- Column 0 is preserved by U (0 ≠ j.succ).
    intro i
    have h0_ne : (0 : Fin (k + 2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    have := hU_pres i 0 h0_ne
    rw [this]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · -- j' < j: column j'.succ preserved by U, divisibility from h_prev.
      have hne : j'.succ ≠ j.succ := by
        intro h
        exact (ne_of_lt hlt) (Fin.succ_inj.mp h)
      have hpres := hU_pres i.succ j'.succ hne
      rw [hpres]
      exact h_prev i j' hlt hj'_lt_i
    · -- j' = j: new clearance from chain-residues output.
      subst heq
      exact hU_clear i hj'_lt_i

/- **Strengthened completion invariant (signature only — not yet proved).**

For the next stint, we will need a stronger one-column step that *also*
preserves a chosen donor column `i_don'` for the *next* target column
`j.succ.succ`. The strengthened statement would read roughly:

```
∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
  (∀ i, N'.1 i 0 = w i) ∧
  (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
    (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) ∧
  (∀ i, N'.1 i i_don' = N.1 i i_don')
```

i.e. the output also leaves column `i_don'` untouched, so that the next
induction step can reuse `i_don'` as its own donor. Since the
underlying clearance `U` only modifies column `j.succ`, this is true
whenever `i_don' ≠ j.succ`. The corresponding lemma
`sl_exists_col_with_chain_compat_donor` would then iterate this
preservation across the whole chain `j = 0, 1, …, k`, threading a
fixed donor column (or a small family of donors) through every step.

We do not land it in this file; the present `sl_clear_one_column_step`
is sufficient to drive the induction once a donor-selection lemma is
available. -/

/-- **Full lower-clearance induction under explicit donor-supply hypothesis.**

Assuming a donor-supply oracle `h_supply` that, for any column `j : Fin (k+1)`
and any partially-cleared `SL` matrix `N` (matching `w` on column 0 and
satisfying lower DivChain divisibilities for columns `j' < j`), produces a
donor index `i_don ≠ j.succ` and chain-compatible per-row residues `c`
sufficient for `sl_clear_one_column_step`, iterate that step across columns
`j = 0, 1, …, k` to obtain a single matrix `N` with first column `w` and
the full lower DivChain clearance.

Proof: induct on `j_max : ℕ` ranging over `0, …, k+1`, producing partial
clearance `j'.val < j_max → j' < i → … ∣ …`. The inductive step at
`j_max < k+1` invokes `h_supply` with `j := ⟨j_max, _⟩` to obtain donor and
residues, then applies `sl_clear_one_column_step`. The conclusion at
`j_max = k+1` is the full lower clearance. -/
private lemma sl_clear_all_columns_of_donor_supply
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol₀ : ∀ i, N₀.1 i 0 = w i)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (∀ i j : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) := by
  suffices h : ∀ j_max : ℕ, j_max ≤ k + 1 →
      ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (∀ i, N.1 i 0 = w i) ∧
        (∀ i j' : Fin (k + 1), j'.val < j_max → j' < i →
          (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)) by
    obtain ⟨N, hcolN, hclear⟩ := h (k + 1) le_rfl
    refine ⟨N, hcolN, ?_⟩
    intro i j' hj'_lt_i
    exact hclear i j' j'.isLt hj'_lt_i
  intro j_max
  induction j_max with
  | zero =>
    intro _
    refine ⟨N₀, hcol₀, ?_⟩
    intro i j' hj' _
    exact absurd hj' (Nat.not_lt_zero _)
  | succ j_max ih =>
    intro hj_max_le
    have hj_max_lt : j_max < k + 1 := Nat.lt_of_succ_le hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, hj_max_lt⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) := by
      intro i j' hj'_lt_j hj'_lt_i
      have : j'.val < j_max := hj'_lt_j
      exact hclear_prev i j' this hj'_lt_i
    obtain ⟨i_don, h_don_ne, c, h_per_row, h_chain_compat⟩ :=
      h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step a ha hda w j N hcolN h_prev
        i_don h_don_ne c h_per_row h_chain_compat
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    have hj'_le_j : j' ≤ j := by
      show j'.val ≤ j.val
      exact Nat.lt_succ_iff.mp hj'_lt_succ
    exact hclear_new i j' hj'_le_j hj'_lt_i

/-- **Conditional consumer.** Bridges `sl_exists_col_of_primitive`,
`sl_clear_all_columns_of_donor_supply`, and
`sl_exists_col_stab_divChain_of_lower_clearance` into one statement: under an
explicit donor-supply oracle (parameterized in the same `(j, N, hcol, h_prev)`
shape as `sl_clear_all_columns_of_donor_supply`), there exists `N` with first
column `w` whose diagonal-conjugate lies in the `GL_pair (k + 2)` stabilizer.

Note (redundancy): superseded by `sl_exists_col_stab_divChain_of_multi_donor_supply`
below, which exposes the more general multi-donor (`c : Fin (k+2) → ℤ`) oracle
shape. The single-donor variant remains available for callers that already
package their column-clearing data in `(i_don, c i)` form. -/
private lemma sl_exists_col_stab_divChain_of_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨N, hcol_N, h_lower⟩ :=
    sl_clear_all_columns_of_donor_supply a ha hda w N₀ hcol₀ h_supply
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol_N h_lower

/-- **Common-`c` reduction.** When the donor-supply oracle can be satisfied
with a single common Bezout coefficient `c0` at each column, the chain
compatibility condition is automatic: take `c i := c0` for all `i`, so
`c i' - c i = 0` is divisible by anything. -/
private lemma h_supply_of_common_c {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ) (c0 : ℤ),
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c0 * N.1 i.succ i_don)) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) := by
  intro j N hcol h_prev
  obtain ⟨i_don, h_don_ne, c0, h_clear⟩ := h_common j N hcol h_prev
  refine ⟨i_don, h_don_ne, fun _ ↦ c0, h_clear, ?_⟩
  intro _ _ _ _
  simp

/-- **Common-`c` bridge.** Specializes `sl_exists_col_stab_divChain_of_donor_supply`
to the case where the donor-supply oracle returns a single common Bezout
coefficient `c0` per column, deferring the chain-compatibility step to
`h_supply_of_common_c`. -/
private lemma sl_exists_col_stab_divChain_of_common_c {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ) (c0 : ℤ),
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c0 * N.1 i.succ i_don)) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_donor_supply a ha hda w hw_primitive hw_col_div
    (h_supply_of_common_c a ha hda w h_common)

/-- **Conditional multi-row, multi-donor column-clearance.** Given a residue
function `c : Fin (k+2) → ℤ` with `c j.succ = 0` and per-row joint divisibility
`(a i / a j) ∣ N i.succ j.succ + ∑ k', c k' * N i.succ k'` for all `i > j`,
realise the cumulative column-effect as a single SL elementary product `U`,
yielding `(N * U)` whose column `j.succ` is now divisible by `(a i / a j)` on
every row `i.succ` with `j < i`, and whose other columns are preserved. This
is the multi-donor analogue of
`sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue`. -/
private lemma sl_clear_one_column_lower_divChain_of_multi_donor
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (c : Fin (k + 2) → ℤ)
    (h_zero : c j.succ = 0)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  obtain ⟨U, hU_pres, hU_target⟩ :=
    sl_addCol_finset_target N j.succ c h_zero
  refine ⟨U, hU_pres, ?_⟩
  intro i hi_lt
  rw [hU_target i.succ]
  exact h_clear i hi_lt

/-- **One-column induction-step wrapper, multi-donor variant.** Mirrors
`sl_clear_one_column_step` but consumes a single residue function `c` (a
combination of all columns) instead of a fixed donor column with chain
compatibility. -/
private lemma sl_clear_one_column_step_multi_donor
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
      (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ))
    (c : Fin (k + 2) → ℤ)
    (h_zero : c j.succ = 0)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) := by
  obtain ⟨U, hU_pres, hU_clear⟩ :=
    sl_clear_one_column_lower_divChain_of_multi_donor
      a ha hda j N c h_zero h_clear
  refine ⟨N * U, ?_, ?_⟩
  · intro i
    have h0_ne : (0 : Fin (k + 2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    have := hU_pres i 0 h0_ne
    rw [this]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · have hne : j'.succ ≠ j.succ := by
        intro h
        exact (ne_of_lt hlt) (Fin.succ_inj.mp h)
      have hpres := hU_pres i.succ j'.succ hne
      rw [hpres]
      exact h_prev i j' hlt hj'_lt_i
    · subst heq
      exact hU_clear i hj'_lt_i

/-- **Full lower-clearance induction under multi-donor supply oracle.** The
multi-donor analogue of `sl_clear_all_columns_of_donor_supply`. Iterates
`sl_clear_one_column_step_multi_donor` across columns `j = 0, 1, …, k`. -/
private lemma sl_clear_all_columns_of_multi_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol₀ : ∀ i, N₀.1 i 0 = w i)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (∀ i j : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) := by
  suffices h : ∀ j_max : ℕ, j_max ≤ k + 1 →
      ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (∀ i, N.1 i 0 = w i) ∧
        (∀ i j' : Fin (k + 1), j'.val < j_max → j' < i →
          (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)) by
    obtain ⟨N, hcolN, hclear⟩ := h (k + 1) le_rfl
    refine ⟨N, hcolN, ?_⟩
    intro i j' hj'_lt_i
    exact hclear i j' j'.isLt hj'_lt_i
  intro j_max
  induction j_max with
  | zero =>
    intro _
    refine ⟨N₀, hcol₀, ?_⟩
    intro i j' hj' _
    exact absurd hj' (Nat.not_lt_zero _)
  | succ j_max ih =>
    intro hj_max_le
    have hj_max_lt : j_max < k + 1 := Nat.lt_of_succ_le hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, hj_max_lt⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) := by
      intro i j' hj'_lt_j hj'_lt_i
      have : j'.val < j_max := hj'_lt_j
      exact hclear_prev i j' this hj'_lt_i
    obtain ⟨c, h_zero, h_clear⟩ := h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step_multi_donor a ha hda w j N hcolN h_prev
        c h_zero h_clear
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    have hj'_le_j : j' ≤ j := by
      show j'.val ≤ j.val
      exact Nat.lt_succ_iff.mp hj'_lt_succ
    exact hclear_new i j' hj'_le_j hj'_lt_i

/-- **Conditional consumer (multi-donor).** Multi-donor analogue of
`sl_exists_col_stab_divChain_of_donor_supply`: bridges
`sl_exists_col_of_primitive`, `sl_clear_all_columns_of_multi_donor_supply`, and
`sl_exists_col_stab_divChain_of_lower_clearance` into one statement. Under a
multi-donor supply oracle (returning a full coefficient vector
`c : Fin (k+2) → ℤ` with `c j.succ = 0` instead of a single donor index), there
exists `N` with first column `w` whose diagonal-conjugate lies in the
`GL_pair (k + 2)` stabilizer.

The remaining mathematical content is the oracle hypothesis `h_supply` itself:
for each target column `j : Fin (k+1)` and each cleared matrix `N`
(satisfying first-column = `w` and the previously-cleared-columns divisibilities
`(a i / a j') ∣ N.1 i.succ j'.succ` for `j' < j < i`), one must produce a
coefficient vector `c : Fin (k+2) → ℤ` with `c j.succ = 0` such that
`(a i / a j) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k'` for every
`i > j`. This is the precise classical multi-row Bezout / SNF arithmetic
oracle that the rest of `sl_exists_col_stab_divChain` reduces to; it is left
as a separate ticket and is *not* discharged here. -/
private lemma sl_exists_col_stab_divChain_of_multi_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨N, hcol_N, h_lower⟩ :=
    sl_clear_all_columns_of_multi_donor_supply a ha hda w N₀ hcol₀ h_supply
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol_N h_lower

/-- **Coordinatewise vector chain CRT.** A vector-valued analogue of
`exists_chain_solution_iff_compatible`: given a chain-ordered modulus
`d : Fin (n + 1) → ℤ` (`d a ∣ d b` for `a ≤ b`) and per-row vectors
`c_per : Fin (n + 1) → Fin n' → ℤ` whose coordinatewise differences satisfy
the chain compatibility `d a ∣ c_per b k - c_per a k` for every coordinate
`k` and every `a ≤ b`, we obtain a single vector `c : Fin n' → ℤ` with
`d a ∣ c k - c_per a k` for every `a` and `k`. The construction simply
takes `c k := c_per (Fin.last n) k`; chain compatibility against the top
index discharges every row simultaneously. -/
private lemma exists_vector_chain_solution
    {n n' : ℕ} (d : Fin (n + 1) → ℤ)
    (_h_chain : ∀ a b : Fin (n + 1), a ≤ b → d a ∣ d b)
    (c_per : Fin (n + 1) → Fin n' → ℤ)
    (h_compat : ∀ a b : Fin (n + 1), a ≤ b → ∀ k : Fin n',
      d a ∣ c_per b k - c_per a k) :
    ∃ c : Fin n' → ℤ, ∀ a : Fin (n + 1), ∀ k : Fin n',
      d a ∣ c k - c_per a k := by
  refine ⟨fun k ↦ c_per (Fin.last n) k, ?_⟩
  intro a k
  exact h_compat a (Fin.last n) (Fin.le_last _) k

/-- **Generic vector avoiding-Bezout to residue.** Given a vector `x : Fin n → ℤ`,
a target index `j` to avoid, and an avoiding Bezout witness `u : Fin n → ℤ` with
`u j = 0` and `∑ k, u k * x k = 1`, we can produce, for any `xj d : ℤ`, a
coefficient vector `c : Fin n → ℤ` with `c j = 0` and `d ∣ xj + ∑ k, c k * x k`.
The construction is `c k := -xj * u k`; then the inner sum equals `-xj`, so the
outer sum is `0`, and any `d` divides `0`. This is the generic linear-algebraic
content underlying `sl_row_clear_mod_avoiding`. -/
private lemma row_clear_avoiding_of_bezout
    {n : ℕ} (x : Fin n → ℤ) (j : Fin n)
    (u : Fin n → ℤ) (h_zero : u j = 0) (h_bez : ∑ k, u k * x k = 1)
    (xj d : ℤ) :
    ∃ c : Fin n → ℤ, c j = 0 ∧ d ∣ xj + ∑ k, c k * x k := by
  refine ⟨fun k ↦ -xj * u k, by simp [h_zero], ?_⟩
  have h_sum : ∑ k, (-xj * u k) * x k = -xj := by
    have h1 : ∑ k, (-xj * u k) * x k = -xj * ∑ k, u k * x k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [h1, h_bez, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero d

/-- **Conditional consumer (row-wise avoiding Bezout to per-row residues).**
Given, for every target column `j`, every cleared matrix `N` with first column
`w`, an externally supplied family `u : Fin (k+1) → Fin (k+2) → ℤ` of avoiding
Bezout witnesses (`u i j.succ = 0`, `∑ k', u i k' * N.1 i.succ k' = 1` for
`j < i`) plus chain compatibility on the constructed family
`c_per_constructed i k' := -(N.1 i.succ j.succ) * u i k'`, we obtain the
`h_per_row` shape consumed by `h_supply_of_row_residues`. The chain
compatibility is asserted on the constructed family rather than on the raw
witnesses because `u_i` and `u_{i'}` are chosen independently per row, and
chain compatibility on `c_per_constructed` is *not* automatic from chain
compatibility on `u`. -/
private lemma h_per_row_via_avoiding_bezout {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_avoiding_compat : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (u : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, u i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', u i k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣
            (-(N.1 i'.succ j.succ) * u i' k') -
              (-(N.1 i.succ j.succ) * u i k')))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k')) := by
  intro j N hcol h_prev
  obtain ⟨u, hu_zero, hu_bez, hu_compat⟩ :=
    h_avoiding_compat j N hcol h_prev
  refine ⟨fun i k' ↦ -(N.1 i.succ j.succ) * u i k', ?_, ?_, ?_⟩
  · intro i
    simp [hu_zero i]
  · intro i hi_lt
    have h_sum : ∑ k', (-(N.1 i.succ j.succ) * u i k') * N.1 i.succ k' =
        -(N.1 i.succ j.succ) := by
      have h1 : ∑ k', (-(N.1 i.succ j.succ) * u i k') * N.1 i.succ k' =
          -(N.1 i.succ j.succ) * ∑ k', u i k' * N.1 i.succ k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k' _ ↦ ?_
        ring
      rw [h1, hu_bez i hi_lt, mul_one]
    rw [h_sum, add_neg_cancel]
    exact dvd_zero _
  · intro i i' hi_lt hi_le k'
    exact hu_compat i i' hi_lt hi_le k'

/-- **Per-row residue oracle reduction.** Packages the per-row data
(coordinate vectors `c_per i : Fin (k + 2) → ℤ`, each annihilating the
target column `j.succ`, each clearing its own row, plus the chain
compatibility `(a i / a j) ∣ c_per i' k' - c_per i k'` for `j < i ≤ i'`)
into the single-vector multi-donor `h_supply` shape consumed by
`sl_exists_col_stab_divChain_of_multi_donor_supply`. The construction takes
`c := c_per (Fin.last k)` and absorbs the row-by-row corrections via the
chain compatibility. -/
private lemma h_supply_of_row_residues {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_per_row : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k'))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k') := by
  intro j N hcol h_prev
  obtain ⟨c_per, h_zero_per, h_clear_per, h_compat⟩ :=
    h_per_row j N hcol h_prev
  refine ⟨fun k' ↦ c_per (Fin.last k) k', h_zero_per (Fin.last k), ?_⟩
  intro i hi_lt
  have hrow := h_clear_per i hi_lt
  have hcompat_k : ∀ k' : Fin (k + 2),
      (((a i / a j : ℕ) : ℤ) ∣ c_per (Fin.last k) k' - c_per i k') := by
    intro k'
    exact h_compat i (Fin.last k) hi_lt (Fin.le_last _) k'
  have hdiff_sum : (((a i / a j : ℕ) : ℤ)) ∣
      ∑ k', (c_per (Fin.last k) k' - c_per i k') * N.1 i.succ k' :=
    Finset.dvd_sum (fun k' _ ↦ (hcompat_k k').mul_right _)
  have hsum := hrow.add hdiff_sum
  have heq : N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k' +
      ∑ k', (c_per (Fin.last k) k' - c_per i k') * N.1 i.succ k' =
      N.1 i.succ j.succ +
        ∑ k', c_per (Fin.last k) k' * N.1 i.succ k' := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k' _
    ring
  rw [heq] at hsum
  exact hsum

/-- **Conditional consumer (per-row residues).** Direct composition of
`h_supply_of_row_residues` with `sl_exists_col_stab_divChain_of_multi_donor_supply`:
under a per-row residue oracle (yielding row-indexed coefficient vectors
satisfying coordinatewise chain compatibility), there exists `N` with first
column `w` whose diagonal-conjugate lies in the `GL_pair (k + 2)` stabilizer. -/
private lemma sl_exists_col_stab_divChain_of_row_residues {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_per_row : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k'))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_multi_donor_supply a ha hda w
    hw_primitive hw_col_div
    (h_supply_of_row_residues a ha hda w h_per_row)

/-- **Common-ν conditional helper.** Assume a SINGLE avoiding Bezout vector `ν`
good for all rows simultaneously, together with a target-column congruence
condition. We derive the `h_avoiding_compat` package shape consumed by
`h_per_row_via_avoiding_bezout`. The construction takes `u i := ν` (the common
witness) for every row; chain compatibility on the constructed family
`c_per i k' := -(N.1 i.succ j.succ) * ν k'` follows because the differences of
target-column entries `N.1 i'.succ j.succ - N.1 i.succ j.succ` are divisible
by `(a i / a j)` by hypothesis, and divisibility is preserved under
multiplication by `-ν k'`. -/
private lemma h_avoiding_compat_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (u : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, u i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', u i k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣
            (-(N.1 i'.succ j.succ) * u i' k') -
              (-(N.1 i.succ j.succ) * u i k'))) := by
  intro j N hcol h_prev
  obtain ⟨ν, hν_zero, hν_bez, hν_col⟩ := h_common j N hcol h_prev
  refine ⟨fun _ k' ↦ ν k', ?_, ?_, ?_⟩
  · intro _; exact hν_zero
  · intro i hi_lt; exact hν_bez i hi_lt
  · intro i i' hi_lt hi_le k'
    have hdvd : (((a i / a j : ℕ) : ℤ)) ∣
        N.1 i'.succ j.succ - N.1 i.succ j.succ := hν_col i i' hi_lt hi_le
    have heq : (-(N.1 i'.succ j.succ) * ν k') - (-(N.1 i.succ j.succ) * ν k')
        = -((N.1 i'.succ j.succ - N.1 i.succ j.succ) * ν k') := by ring
    rw [heq]
    exact (hdvd.mul_right _).neg_right

/-- **Conditional consumer (common-ν to per-row residues).** Direct composition
of `h_avoiding_compat_of_common_nu` with `h_per_row_via_avoiding_bezout`. -/
private lemma h_per_row_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k')) :=
  h_per_row_via_avoiding_bezout a ha hda w
    (h_avoiding_compat_of_common_nu a ha hda w h_common)

/-- **Final conditional consumer (common-ν to H-membership).** Direct composition
of `h_per_row_of_common_nu` with `sl_exists_col_stab_divChain_of_row_residues`. -/
private lemma sl_exists_col_stab_divChain_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_row_residues a ha hda w hw_primitive hw_col_div
    (h_per_row_of_common_nu a ha hda w h_common)

/- **Remaining oracle (precise statement of the open arithmetic content).**
The two outstanding `sorry`s in this file (`sl_exists_col_stab_divChain` at
~L4178 and `fiber_has_block_form_preimages` at ~L4206) both reduce, via
`sl_exists_col_stab_divChain_of_multi_donor_supply`, to the following
self-contained classical arithmetic claim:

  Given:
    * `k : ℕ`,
    * a positive divisor chain `a : Fin (k+1) → ℕ` with `a i ∣ a (i+1)`,
    * a primitive vector `w : Fin (k+2) → ℤ` with `(a i) ∣ w i.succ`,
    * a target column index `j : Fin (k+1)`,
    * an `SL_{k+2}(ℤ)` matrix `N` with first column `w` and with the previous
      columns already cleared:
        `∀ i j' : Fin (k+1), j' < j → j' < i → (a i / a j') ∣ N.1 i.succ j'.succ`,

  Find a coefficient vector `c : Fin (k+2) → ℤ` with `c j.succ = 0` and
        `∀ i : Fin (k+1), j < i → (a i / a j) ∣ N.1 i.succ j.succ +
                                   ∑ k', c k' * N.1 i.succ k'`.

This is a multi-row simultaneous Bezout / SNF column-reduction problem on the
columns ≠ `j.succ` of `N` (the `c j.succ = 0` constraint forbids touching the
target column itself). The natural proof packages a finite-row CRT step
(cf. `sl_addCol_make_dvd_finset`) with the divisor-chain compatibility
`(a i / a j) ∣ (a i' / a j)` for `i ≤ i'`, exploiting that the rows below `j`
form a `det = ±1` block whose entries can be made coprime to the target moduli
`(a i / a j)`. It is the *only* remaining mathematical content needed to
discharge `sl_exists_col_stab_divChain` (and, transitively,
`fiber_has_block_form_preimages`) — every other reduction in this section is
already in place. The oracle is intentionally left open here; downstream
infrastructure (`sl_clear_all_columns_of_multi_donor_supply`,
`sl_exists_col_stab_divChain_of_multi_donor_supply`,
`sl_exists_col_stab_divChain_of_lower_clearance`) consumes it directly. -/

/- **T001 diagnosis (2026-04-25): the `h_common` reduction route is too strong.**

The conditional consumer `sl_exists_col_stab_divChain_of_common_nu` reduces the
oracle to a "common avoiding-Bezout vector" hypothesis `h_common` (cf.
`h_avoiding_compat_of_common_nu`, `h_per_row_of_common_nu`). For an arbitrary
`SL_{k+2}(ℤ)` matrix `N` with first column `w` and previous columns `j' < j`
cleared, `h_common` demands a SINGLE coefficient vector `ν : Fin (k + 2) → ℤ`
with `ν j.succ = 0` such that *for every row* `i > j`,
  `∑ k', ν k' * N.1 i.succ k' = 1`,
PLUS a target-column congruence
  `(a i / a j) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ`  for `j < i ≤ i'`.

Both conjuncts are FALSE for generic `N`:

(A) **No common Bezout-`1` vector across rows in general.** Writing `M` for the
    `((k + 1 - j) × (k + 2))` submatrix of rows `i > j` of `N.1.succ`, the
    constraint `M · ν = 𝟙` with `ν j.succ = 0` is a ℤ-linear system on the
    `(k + 1)`-dimensional subspace `{ν : ν j.succ = 0}`. For `j = 0` and
    `k ≥ 1` (so at least 2 rows below), choose `N` whose lower rows are linearly
    dependent modulo a prime `p` (always achievable inside `SL_{k+2}(ℤ)` by row
    operations *on rows above* `0` — those rows are free for the consumer to
    pick). Then `M ν ≡ (c, c, …)ᵀ (mod p)` for a single scalar `c`, so
    `(1, 1, …, 1)ᵀ` is unreachable mod `p`. This is precisely the Smith normal
    form obstruction: the gcd of the maximal minors of `M` (excluding column
    `j.succ`) need not be `1`.

(B) **The target-column congruence is not maintained by the iterative loop.**
    `sl_clear_all_columns_of_multi_donor_supply` enters column `j` with
    `N.1 i.succ j.succ` already mutated by the previous `j' < j` clearing
    steps; those steps perform unrestricted row-additions among rows
    `j' < i ≤ k`, and have no mechanism to enforce
    `(a i / a j) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ`. Concretely, the
    column-`j` clearing step uses `sl_clear_one_column_step_multi_donor`, which
    is silent about column `j.succ`.

Conclusion: the `_of_common_nu` reduction layer is a CONVENIENCE wrapper for
the case where `N` happens to admit a common Bezout vector — it is NOT a
sufficient route to discharge the open oracle.

**Recommended next-stint approach (does not pass through `h_common`):**

1. Build `N₀` not from generic `sl_exists_col_of_primitive`, but from a
   Smith- or Hermite-normal-form construction: produce `N₀ ∈ SL_{k+2}(ℤ)` with
   first column `w` AND with the lower `(k + 1) × (k + 1)` block `B` already
   in column-Hermite form. Then for each `j`, the `j`-th column of `B` is
   `(a j / a 0, …)ᵀ`-aligned, and the per-row Bezout step reduces to a
   one-row coprimality fact (`gcd(B i j, …) = 1`) inherited from
   `det B = ±1`.

2. Alternatively, replace the oracle entirely by an iterative refinement
   `N_j ∈ SL_{k+2}(ℤ)` (one per `j`) maintaining the explicit invariant
   "lower block is Hermite-reduced through column `j - 1`". This bypasses the
   need for any per-step Bezout common vector: the SNF/HNF reduction supplies
   the divisor-chain divisibility directly via column operations.

3. Either approach uses `sl_addCol_make_dvd_finset` only as a single-row
   tool, never asking it to satisfy a multi-row simultaneous constraint.

The current file's `_of_common_nu`/`_of_row_residues`/`_of_multi_donor_supply`
chain is preserved as scaffolding (its other consumers may still be useful),
but the open `sl_exists_col_stab_divChain` (k ≥ 1) cannot be discharged
through `h_common`. A future stint should target the HNF approach above. -/

/-- **Base case `k = 0`.** At dim 2, the lower-clearance condition is vacuous
(no `i, j : Fin 1` with `j < i`), so the conclusion follows immediately from
`sl_exists_col_of_primitive` and `sl_exists_col_stab_divChain_of_lower_clearance`. -/
private lemma sl_exists_col_stab_divChain_zero
    (a : Fin 1 → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain 1 a)
    (w : Fin 2 → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin 1, (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin 2) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat 2 (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin 2) ℚ) *
        diagMat 2 (Fin.cons 1 a) ∈ (GL_pair 2).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  refine sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N₀ hcol₀ ?_
  intro i j hji
  have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
  simp only [Fin.lt_def, hj, hi, lt_irrefl] at hji

/-- **Strengthened completion target.**  An `N ∈ SL_{k+2}(ℤ)` with prescribed
first column `w` AND with strictly-lower-triangular entries (below the leading
column) satisfying the `a i / a j` divisibility chain.  This is exactly the
data consumed by `sl_exists_col_stab_divChain_of_lower_clearance`. -/
private def StrengthenedCompletionTarget {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ) : Prop :=
  ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
    (∀ i, N.1 i 0 = w i) ∧
    (∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ))

/-- **Conditional reduction.**  If a `StrengthenedCompletionTarget` exists for
`(a, w)`, then the desired stabilizer-membership conclusion of
`sl_exists_col_stab_divChain` holds.  This isolates the remaining blocker as
the structured-completion existence problem. -/
private lemma sl_exists_col_stab_divChain_of_strengthened_completion {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_completion : StrengthenedCompletionTarget a w) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N, hcol, h_lower⟩ := h_completion
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol h_lower

/-- **SNF bridge for a square integer matrix with positive determinant.**
A repackaging of `exists_diagonal_of_posdet`: every `A : Matrix (Fin n) (Fin n) ℤ`
with `0 < det A` is `SL_n(ℤ)`-equivalent (on both sides) to a positive diagonal.
Exposed in `(L, R, d)` form for downstream completion-construction use. -/
private lemma exists_diagonal_of_posdet_for_lower_block {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ) (d : Fin n → ℤ),
      (∀ i, 0 < d i) ∧
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
        Matrix.diagonal d := by
  obtain ⟨d, hd_pos, L, R, hLR⟩ := exists_diagonal_of_posdet (n := n) A hdet
  exact ⟨L, R, d, hd_pos, hLR⟩

/-! ### Trailing-block HNF interface (column-HNF route)

The remaining open theorem `sl_exists_col_stab_divChain` at `k ≥ 1` reduces to the
construction of an `SL_{k+1}(ℤ)` matrix `R` that puts the trailing
`(k+2) × (k+1)` block of an arbitrary `SL_{k+2}(ℤ)` extension `N₀` of `w` into
"column-HNF" form satisfying the `a i / a j` divisibility chain. The interface
below packages this as `TrailingBlockHNFData a w` and provides the structural
consumer producing a `StrengthenedCompletionTarget`. The remaining open piece —
the existence of such an `R` — is exactly the trailing-block HNF construction
(an SL-version of column-Hermite-normal-form preserving the divisibility chain).

The block matrix `slSuccEmbed R` (already developed above) gives the SL-version
of the block diagonal `[[1, 0], [0, R]] ∈ SL_{k+2}(ℤ)`. Its right-action on
`N₀ ∈ SL_{k+2}(ℤ)` preserves column 0 (because column 0 of `slSuccEmbed R` is
`e₀`) and reshapes the trailing block via right-multiplication by `R`. -/

/-- **Right-multiplication by `slSuccEmbed R` preserves column 0** of any
`SL_{k+2}(ℤ)` matrix. This is the structural property that ordinary square SNF
lacked: it lets us improve the trailing block of an extension `N₀` of a vector
`w` without disturbing the prescribed first column. -/
private lemma slSuccEmbed_preserves_col_zero {k : ℕ}
    (R : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ) (i : Fin (k + 2)) :
    (N₀ * slSuccEmbed R).1 i 0 = N₀.1 i 0 := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  rw [slSuccEmbed_val_zero_zero, mul_one]
  have hzero : ∀ j : Fin (k + 1),
      N₀.1 i j.succ * (slSuccEmbed R).1 j.succ 0 = 0 := by
    intro j; rw [slSuccEmbed_val_succ_zero]; ring
  simp [hzero]

/-! ### 2-column Bezout reduction helper (T001)

The `bezout2` matrix below is the elementary 2-column operation that, embedded
into `SL (Fin (k+1)) ℤ` via a block scheme and then via `slSuccEmbed` into
`SL (Fin (k+2)) ℤ`, reduces a single pair of columns of the trailing block.
Iterating column-by-column produces a column-HNF for the trailing block.

Right-multiplying the row vector `[x, y]` by `bezout2 x y` yields the row
`[Int.gcd x y, 0]`. When `Int.gcd x y = 0` (equivalently `x = y = 0`) the
matrix collapses to the identity.
-/

/-- The 2×2 Bezout reduction matrix. Right-multiplication by this matrix sends
the row `[x, y]` to `[Int.gcd x y, 0]`. -/
private def bezout2 (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (Int.gcd x y : ℤ) = 0 then 1 else
  !![Int.gcdA x y, -y / (Int.gcd x y : ℤ);
     Int.gcdB x y,  x / (Int.gcd x y : ℤ)]

/-- Row action of `bezout2` on the first column gives `Int.gcd x y`. -/
private lemma bezout2_action_col0 (x y : ℤ) :
    x * (bezout2 x y) 0 0 + y * (bezout2 x y) 1 0 = (Int.gcd x y : ℤ) := by
  unfold bezout2
  by_cases hg : (Int.gcd x y : ℤ) = 0
  · rw [if_pos hg]
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at hg
    simp [hg.1, hg.2]
  · rw [if_neg hg]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    have := Int.gcd_eq_gcd_ab x y
    linarith

/-- Row action of `bezout2` on the second column gives `0`. -/
private lemma bezout2_action_col1 (x y : ℤ) :
    x * (bezout2 x y) 0 1 + y * (bezout2 x y) 1 1 = 0 := by
  unfold bezout2
  by_cases hg : (Int.gcd x y : ℤ) = 0
  · rw [if_pos hg]
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at hg
    simp [hg.1, hg.2]
  · rw [if_neg hg]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    have hxg : (Int.gcd x y : ℤ) ∣ x := Int.gcd_dvd_left x y
    have hyg : (Int.gcd x y : ℤ) ∣ y := Int.gcd_dvd_right x y
    set g : ℤ := (Int.gcd x y : ℤ) with hg_def
    obtain ⟨a, ha⟩ := hxg
    obtain ⟨b, hb⟩ := hyg
    rw [ha, hb, show -(g * b) = g * (-b) by ring,
        Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
    ring

/-- The 2×2 Bezout reduction matrix has determinant `1` whenever
`Int.gcd x y ≠ 0`. -/
private lemma bezout2_det (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    (bezout2 x y).det = 1 := by
  unfold bezout2
  rw [if_neg hg, Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
  have hxg : (Int.gcd x y : ℤ) ∣ x := Int.gcd_dvd_left x y
  have hyg : (Int.gcd x y : ℤ) ∣ y := Int.gcd_dvd_right x y
  have hbez := Int.gcd_eq_gcd_ab x y
  set g : ℤ := (Int.gcd x y : ℤ) with hg_def
  obtain ⟨a, ha⟩ := hxg
  obtain ⟨b, hb⟩ := hyg
  have hbez' : g * (Int.gcdA x y * a + Int.gcdB x y * b) = g * 1 := by
    rw [mul_one, mul_add]
    calc g * (Int.gcdA x y * a) + g * (Int.gcdB x y * b)
        = (g * a) * Int.gcdA x y + (g * b) * Int.gcdB x y := by ring
      _ = x * Int.gcdA x y + y * Int.gcdB x y := by rw [← ha, ← hb]
      _ = g := by linarith [hbez]
  have h1 : Int.gcdA x y * a + Int.gcdB x y * b = 1 := mul_left_cancel₀ hg hbez'
  rw [ha, hb, show -(g * b) = g * (-b) by ring,
      Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
  rw [← ha, ← hb]
  linarith

/-- `SL₂(ℤ)` packaging of the 2×2 Bezout reduction matrix, valid when
`Int.gcd x y ≠ 0`. -/
private noncomputable def bezout2SL (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    SpecialLinearGroup (Fin 2) ℤ :=
  ⟨bezout2 x y, bezout2_det x y hg⟩

/-! ### Trailing-pair Bezout embedding into `SL(Fin (r + 2)) ℤ`

The 2×2 Bezout reduction matrix `bezout2SL x y hg` lifts to an
`SL(Fin (r + 2)) ℤ` matrix that acts as `bezout2 x y` on the last two
indices and as the identity on the leading `r × r` block. The
construction is by recursion on `r`, using the block embedding
`slSuccEmbed` which prepends a `1`-row/column to the front. -/

/-- The trailing-pair Bezout embedding: an `SL(Fin (r + 2)) ℤ` matrix that
acts as `bezout2 x y` on the trailing `2 × 2` block (indices
`Fin.natAdd r i` for `i : Fin 2`) and as the identity on the leading
`r × r` block. -/
private noncomputable def bezout2TrailingSL : (r : ℕ) → (x y : ℤ) →
    ((Int.gcd x y : ℤ) ≠ 0) → SpecialLinearGroup (Fin (r + 2)) ℤ
  | 0,     x, y, hg => bezout2SL x y hg
  | r + 1, x, y, hg => slSuccEmbed (bezout2TrailingSL r x y hg)

/-- Defining equation for `bezout2TrailingSL` at `r = 0`. -/
private lemma bezout2TrailingSL_zero (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL 0 x y hg = bezout2SL x y hg := rfl

/-- Defining equation for `bezout2TrailingSL` at `r + 1`: prepend a `1`-row
and `1`-column via `slSuccEmbed`. -/
private lemma bezout2TrailingSL_succ (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL (r + 1) x y hg =
      slSuccEmbed (bezout2TrailingSL r x y hg) := rfl

/-- **Trailing block entries.** The `(Fin.natAdd r i, Fin.natAdd r j)` entry
of `bezout2TrailingSL r x y hg` is exactly the `(i, j)` entry of the
underlying `2 × 2` Bezout matrix `bezout2 x y`. This is the central
action lemma describing the trailing-pair behavior. -/
private lemma bezout2TrailingSL_val_natAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i j : Fin 2) :
    (bezout2TrailingSL r x y hg).val (Fin.natAdd r i) (Fin.natAdd r j) =
      bezout2 x y i j := by
  induction r with
  | zero =>
    have hi : (Fin.natAdd 0 i : Fin (0 + 2)) = i := by ext; simp [Fin.natAdd]
    have hj : (Fin.natAdd 0 j : Fin (0 + 2)) = j := by ext; simp [Fin.natAdd]
    rw [hi, hj, bezout2TrailingSL_zero]
    rfl
  | succ r ih =>
    have hi : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
      ext; simp [Fin.natAdd, Fin.succ]; ring
    have hj : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
      ext; simp [Fin.natAdd, Fin.succ]; ring
    rw [bezout2TrailingSL_succ, hi, hj, slSuccEmbed_val_succ_succ, ih]

/-- **Top-left identity block.** On the leading `r × r` block (indices
`Fin.castAdd 2 i` and `Fin.castAdd 2 j` for `i j : Fin r`), the matrix
`bezout2TrailingSL r x y hg` agrees with the identity. -/
private lemma bezout2TrailingSL_val_castAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i j : Fin r) :
    (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 i) (Fin.castAdd 2 j) =
      if i = j then 1 else 0 := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        show (slSuccEmbed _).val (Fin.castAdd 2 (0 : Fin (r+1)))
          (Fin.castAdd 2 (0 : Fin (r+1))) = _
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        rw [h0, slSuccEmbed_val_zero_zero]
        simp
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        have hsucc : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [h0, hsucc, slSuccEmbed_val_zero_succ]
        exact (if_neg (Fin.succ_ne_zero j').symm).symm
    · rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        have hsucc : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [h0, hsucc, slSuccEmbed_val_succ_zero]
        have : i'.succ ≠ 0 := Fin.succ_ne_zero _
        simp [this]
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have hsucci : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
        have hsuccj : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [hsucci, hsuccj, slSuccEmbed_val_succ_succ, ih]
        by_cases h : i' = j' <;> simp [h, Fin.succ_inj]

/-- **Mixed top-right block: identity rows are zero past the diagonal.**
On the leading-row / trailing-column block, the matrix is zero. -/
private lemma bezout2TrailingSL_val_castAdd_natAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i : Fin r) (j : Fin 2) :
    (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 i) (Fin.natAdd r j) = 0 := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · subst hi
      rw [bezout2TrailingSL_succ]
      have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
        ext; simp [Fin.castAdd]
      have hjs : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [h0, hjs, slSuccEmbed_val_zero_succ]
    · subst hi
      rw [bezout2TrailingSL_succ]
      have hsucci : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
          (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
      have hjs : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [hsucci, hjs, slSuccEmbed_val_succ_succ, ih]

/-- **Mixed bottom-left block: identity columns are zero past the diagonal.**
On the trailing-row / leading-column block, the matrix is zero. -/
private lemma bezout2TrailingSL_val_natAdd_castAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i : Fin 2) (j : Fin r) :
    (bezout2TrailingSL r x y hg).val (Fin.natAdd r i) (Fin.castAdd 2 j) = 0 := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
    · subst hj
      rw [bezout2TrailingSL_succ]
      have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
        ext; simp [Fin.castAdd]
      have his : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [h0, his, slSuccEmbed_val_succ_zero]
    · subst hj
      rw [bezout2TrailingSL_succ]
      have hsuccj : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
          (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
      have his : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [hsuccj, his, slSuccEmbed_val_succ_succ, ih]

/-- **Row action of `bezout2TrailingSL` on the trailing column 0.**
For a row `i` of `M` whose trailing pair is `(x, y)`, right-multiplication by
`bezout2TrailingSL r x y hg` produces `Int.gcd x y` at the `Fin.natAdd r 0`
position. -/
private lemma row_mul_bezout2TrailingSL_natAdd_zero {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n)
    (hxx : M i (Fin.natAdd r 0) = x) (hyy : M i (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 0) =
      (Int.gcd x y : ℤ) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 0) =
        (Int.gcd x y : ℤ) := by
    rw [Fin.sum_univ_two]
    rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd, hxx, hyy]
    exact bezout2_action_col0 x y
  rw [hcast, hnat, zero_add]

/-- **Row action of `bezout2TrailingSL` on the trailing column 1.**
For a row `i` of `M` whose trailing pair is `(x, y)`, right-multiplication by
`bezout2TrailingSL r x y hg` produces `0` at the `Fin.natAdd r 1`
position. -/
private lemma row_mul_bezout2TrailingSL_natAdd_one {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n)
    (hxx : M i (Fin.natAdd r 0) = x) (hyy : M i (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 1) = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 1) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 1) = 0 := by
    rw [Fin.sum_univ_two]
    rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd, hxx, hyy]
    exact bezout2_action_col1 x y
  rw [hcast, hnat, zero_add]

/-- **Preservation of leading columns by `bezout2TrailingSL`.**
Right-multiplication by `bezout2TrailingSL r x y hg` does not alter the
leading `r` columns of `M` (those indexed by `Fin.castAdd 2 j` for `j : Fin r`). -/
private lemma col_mul_bezout2TrailingSL_castAdd {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n) (j : Fin r) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.castAdd 2 j) =
      M i (Fin.castAdd 2 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.castAdd 2 j) =
        M i (Fin.castAdd 2 j) := by
    rw [Finset.sum_eq_single j]
    · rw [bezout2TrailingSL_val_castAdd, if_pos rfl, mul_one]
    · intro k _ hk
      rw [bezout2TrailingSL_val_castAdd, if_neg hk, mul_zero]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.castAdd 2 j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_natAdd_castAdd, mul_zero]
  rw [hcast, hnat, add_zero]


/-- **Trailing-block HNF data** for `(a, w)`. This packages exactly the data
needed to build a `StrengthenedCompletionTarget`: an arbitrary SL-extension `N₀`
of `w` (col 0 = `w`) together with an `SL_{k+1}(ℤ)` transformation `R` whose
right-action on the trailing `(k+2) × (k+1)` block of `N₀` produces the
`a i / a j` divisibility chain. The block diagonal `slSuccEmbed R` preserves col 0
(`slSuccEmbed_preserves_col_zero`), so the product `N₀ * slSuccEmbed R` is the
desired strengthened completion. -/
private def TrailingBlockHNFData {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ) : Prop :=
  ∃ (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (R : SpecialLinearGroup (Fin (k + 1)) ℤ),
    (∀ i, N₀.1 i 0 = w i) ∧
    (∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣
        ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j))

/-- **Conditional consumer.** From `TrailingBlockHNFData a w`, build a
`StrengthenedCompletionTarget a w`. The construction is `N := N₀ * slSuccEmbed R`:
column 0 is preserved by `slSuccEmbed_preserves_col_zero`, and the trailing
divisibility comes from the `R`-witness in `TrailingBlockHNFData`. -/
private lemma strengthenedCompletionTarget_of_trailing_hnf_data {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (h : TrailingBlockHNFData a w) :
    StrengthenedCompletionTarget a w := by
  obtain ⟨N₀, R, hcol₀, h_div⟩ := h
  refine ⟨N₀ * slSuccEmbed R, ?_, ?_⟩
  · intro i
    rw [slSuccEmbed_preserves_col_zero R N₀ i]
    exact hcol₀ i
  · intro i j hji
    have hentry :
        (N₀ * slSuccEmbed R).1 i.succ j.succ =
          ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j := by
      simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      rw [Fin.sum_univ_succ]
      rw [slSuccEmbed_val_zero_succ, mul_zero, zero_add]
      refine Finset.sum_congr rfl ?_
      intro k' _
      rw [slSuccEmbed_val_succ_succ]
    rw [hentry]
    exact h_div i j hji

/-- **Conditional consumer for `TrailingBlockHNFData`.** Composing
`strengthenedCompletionTarget_of_trailing_hnf_data` with
`sl_exists_col_stab_divChain_of_strengthened_completion` gives the desired
SL stabilizer-membership statement directly from a `TrailingBlockHNFData`
witness. This is the named clean target for downstream HNF-construction work.
Note: `hw_primitive` is absorbed into the `N₀` field of `TrailingBlockHNFData`
(any SL-extension of `w` exists iff `w` is primitive). -/
private lemma sl_exists_col_stab_divChain_of_trailing_hnf_data {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h : TrailingBlockHNFData a w) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  exact sl_exists_col_stab_divChain_of_strengthened_completion a ha hda w hw_col_div
    (strengthenedCompletionTarget_of_trailing_hnf_data a w h)

/-- **Bridge: `StrengthenedCompletionTarget` implies `TrailingBlockHNFData`.**
The trailing-block HNF route with `R = 1` (identity in `SL_{k+1}(ℤ)`) is sufficient
to recover any `StrengthenedCompletionTarget`: take `N₀ := N` (the strengthened
completion) and `R := 1`. The trailing-block sum `∑ k', N.1 i.succ k'.succ * R.1 k' j`
collapses to `N.1 i.succ j.succ` since the identity matrix is supported on the
diagonal, and the strengthened completion's lower-triangular divisibility supplies
the divisibility witness.

This makes explicit that `StrengthenedCompletionTarget` and `TrailingBlockHNFData`
are equivalent (the forward direction is `strengthenedCompletionTarget_of_trailing_hnf_data`),
isolating the open existence question to either of the two equivalent forms. -/
private lemma trailingBlockHNFData_of_strengthenedCompletionTarget {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (h : StrengthenedCompletionTarget a w) :
    TrailingBlockHNFData a w := by
  obtain ⟨N, hcol, h_div⟩ := h
  refine ⟨N, 1, hcol, ?_⟩
  intro i j hji
  have hsum :
      ∑ k' : Fin (k + 1), N.1 i.succ k'.succ *
          (1 : SpecialLinearGroup (Fin (k + 1)) ℤ).1 k' j =
        N.1 i.succ j.succ := by
    simp [SpecialLinearGroup.coe_one, Matrix.one_apply, Finset.sum_ite_eq']
  rw [hsum]
  exact h_div i j hji

/-! ### Column-HNF iteration: explicit remaining gap

The construction of `TrailingBlockHNFData a w` from `hw_primitive` + `hw_col_div`
reduces — via `sl_exists_col_of_primitive` — to producing, for any chosen SL
completion `N₀` of `w` (col 0 = `w`), a transformation `R : SL_{k+1}(ℤ)` whose
right-action on the trailing `(k+2) × (k+1)` block of `N₀` enforces the
`(a i / a j)`-divisibility chain on strict-lower entries.

The honest remaining theorem is:

```
∀ (a : Fin (k+1) → ℕ) (hda : DivChain (k+1) a)
  (N₀ : SpecialLinearGroup (Fin (k+2)) ℤ),
  ∃ R : SpecialLinearGroup (Fin (k+1)) ℤ,
    ∀ i j : Fin (k+1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣
        ∑ k' : Fin (k+1), N₀.1 i.succ k'.succ * R.1 k' j)
```

The construction is column-HNF iteration on the trailing block: iterate the
one-step Bezout adapter `sl_mul_slSuccEmbed_bezout2TrailingSL_apply` to clear
above-diagonal entries within each column while preserving lower divisibility,
producing a finite product of `slSuccEmbed (bezout2TrailingSL …)` factors whose
combined right-action delivers `R`.

The conditional helper `trailingBlockHNFData_of_R_existence` below converts
this hypothesis into a `TrailingBlockHNFData` witness, isolating the remaining
arithmetic content. -/

/-- **Conditional helper for `TrailingBlockHNFData`.** Given the existence,
for **every** SL completion `N₀` of `w` (col 0 = `w`), of an
`R : SL_{k+1}(ℤ)` such that the right-action of `R` on the trailing block of
`N₀` enforces the `(a i / a j)`-divisibility chain on strict-lower entries,
package the resulting data into `TrailingBlockHNFData a w`.

The proof obtains a canonical `N₀` from `sl_exists_col_of_primitive`, applies
the hypothesis to extract `R`, and packages the pair into a
`TrailingBlockHNFData` witness.

This helper expresses cleanly the column-HNF iteration content as the only
remaining open piece: the existence of `R` is the genuine remaining
mathematics. The hypothesis is stated "for every `N₀`" (rather than for the
specific witness of `sl_exists_col_of_primitive`) because the existence of
the column-HNF reduction is a generic statement about SL extensions, not
tied to a particular completion. -/
private lemma trailingBlockHNFData_of_R_existence {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (h_R : ∀ N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N₀.1 i 0 = w i) →
      ∃ R : SpecialLinearGroup (Fin (k + 1)) ℤ,
        ∀ i j : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j)) :
    TrailingBlockHNFData a w := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨R, hR⟩ := h_R N₀ hcol₀
  exact ⟨N₀, R, hcol₀, hR⟩

/-- **Honest one-step trailing-pair update.** Right-multiplication of `M` by
`bezout2TrailingSL r x y hg` (with `(x, y)` chosen as the trailing pair of a
target row `i_target`) has exactly five effects:

1. The target row's final pair becomes `(gcd x y, 0)`.
2. The first `r` columns are preserved for **every** row.
3-5. Other rows' final two entries become explicit linear combinations of their
     own trailing pair via the `bezout2 x y` entries — they are **not**
     preserved in general. -/
private lemma matrix_mul_bezout2TrailingSL_apply {n r : ℕ}
    (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ)
    (i_target : Fin n)
    (hxx : M i_target (Fin.natAdd r 0) = x)
    (hyy : M i_target (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i_target (Fin.natAdd r 0) =
        (Int.gcd x y : ℤ) ∧
    (M * (bezout2TrailingSL r x y hg).val) i_target (Fin.natAdd r 1) = 0 ∧
    (∀ i : Fin n, ∀ j : Fin r,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.castAdd 2 j) =
        M i (Fin.castAdd 2 j)) ∧
    (∀ i : Fin n,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 0) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 0 +
        M i (Fin.natAdd r 1) * (bezout2 x y) 1 0) ∧
    (∀ i : Fin n,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 1) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 1 +
        M i (Fin.natAdd r 1) * (bezout2 x y) 1 1) := by
  refine ⟨row_mul_bezout2TrailingSL_natAdd_zero x y hg M i_target hxx hyy,
          row_mul_bezout2TrailingSL_natAdd_one  x y hg M i_target hxx hyy,
          fun i j ↦ col_mul_bezout2TrailingSL_castAdd x y hg M i j,
          ?_, ?_⟩
  · -- Trailing column 0, arbitrary row: linear combination via bezout2.
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    have hcast : ∑ k : Fin r,
        M i (Fin.castAdd 2 k) *
          (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
    have hnat : ∑ k : Fin 2,
        M i (Fin.natAdd r k) *
          (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 0) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 0 +
          M i (Fin.natAdd r 1) * (bezout2 x y) 1 0 := by
      rw [Fin.sum_univ_two]
      rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd]
    rw [hcast, hnat, zero_add]
  · -- Trailing column 1, arbitrary row: linear combination via bezout2.
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    have hcast : ∑ k : Fin r,
        M i (Fin.castAdd 2 k) *
          (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 1) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
    have hnat : ∑ k : Fin 2,
        M i (Fin.natAdd r k) *
          (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 1) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 1 +
          M i (Fin.natAdd r 1) * (bezout2 x y) 1 1 := by
      rw [Fin.sum_univ_two]
      rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd]
    rw [hcast, hnat, zero_add]

/-- **Bridge: trailing-block product through `slSuccEmbed`.** For
`N₀ : SL_{r+3}(ℤ)` and `U : SL_{r+2}(ℤ)`, the `(i.succ, j.succ)` entry of
`N₀ * slSuccEmbed U` equals the `(i, j)` entry of `M * U.val`, where `M` is the
trailing `(r+2) × (r+2)` block of `N₀` (`M i j := N₀.1 i.succ j.succ`).

This is the structural identity that lets `matrix_mul_bezout2TrailingSL_apply`
be transported from the bare matrix level to the `SL` product
`N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)`. -/
private lemma N₀_mul_slSuccEmbed_apply_succ_succ {r : ℕ}
    (N₀ : SpecialLinearGroup (Fin (r + 3)) ℤ)
    (U : SpecialLinearGroup (Fin (r + 2)) ℤ)
    (i j : Fin (r + 2)) :
    (N₀ * slSuccEmbed U).1 i.succ j.succ =
      ∑ k' : Fin (r + 2), N₀.1 i.succ k'.succ * U.val k' j := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  rw [slSuccEmbed_val_zero_succ, mul_zero, zero_add]
  refine Finset.sum_congr rfl ?_
  intro k' _
  rw [slSuccEmbed_val_succ_succ]

/-- **Matrix-level Bezout one-step transported to `N₀ * slSuccEmbed U`.**
Given `N₀ : SL_{r+3}(ℤ)` and a target trailing row `i_target : Fin (r+2)` whose
final pair `(N₀.1 i_target.succ (Fin.natAdd r 0).succ,
N₀.1 i_target.succ (Fin.natAdd r 1).succ)` equals `(x, y)`, right-multiplication
by `slSuccEmbed (bezout2TrailingSL r x y hg)` has the four expected effects:
column 0 preserved, the first `r` trailing columns preserved on every trailing
row, the target trailing pair becomes `(gcd, 0)`, and every other trailing row's
final pair is the `bezout2`-linear combination of its old final pair. -/
private lemma sl_mul_slSuccEmbed_bezout2TrailingSL_apply {r : ℕ}
    (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0)
    (N₀ : SpecialLinearGroup (Fin (r + 3)) ℤ)
    (i_target : Fin (r + 2))
    (hxx : N₀.1 i_target.succ (Fin.natAdd r 0).succ = x)
    (hyy : N₀.1 i_target.succ (Fin.natAdd r 1).succ = y) :
    let N₁ := N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)
    (∀ i : Fin (r + 3), N₁.1 i 0 = N₀.1 i 0) ∧
    (∀ i : Fin (r + 2), ∀ j : Fin r,
      N₁.1 i.succ (Fin.castAdd 2 j).succ = N₀.1 i.succ (Fin.castAdd 2 j).succ) ∧
    N₁.1 i_target.succ (Fin.natAdd r 0).succ = (Int.gcd x y : ℤ) ∧
    N₁.1 i_target.succ (Fin.natAdd r 1).succ = 0 ∧
    (∀ i : Fin (r + 2),
      N₁.1 i.succ (Fin.natAdd r 0).succ =
        N₀.1 i.succ (Fin.natAdd r 0).succ * (bezout2 x y) 0 0 +
        N₀.1 i.succ (Fin.natAdd r 1).succ * (bezout2 x y) 1 0) ∧
    (∀ i : Fin (r + 2),
      N₁.1 i.succ (Fin.natAdd r 1).succ =
        N₀.1 i.succ (Fin.natAdd r 0).succ * (bezout2 x y) 0 1 +
        N₀.1 i.succ (Fin.natAdd r 1).succ * (bezout2 x y) 1 1) := by
  set M : Matrix (Fin (r + 2)) (Fin (r + 2)) ℤ :=
    Matrix.of (fun i j ↦ N₀.1 i.succ j.succ) with hM_def
  have hbridge : ∀ i j : Fin (r + 2),
      (N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)).1 i.succ j.succ =
        (M * (bezout2TrailingSL r x y hg).val) i j := by
    intro i j
    rw [N₀_mul_slSuccEmbed_apply_succ_succ]
    simp [Matrix.mul_apply, hM_def]
  have hxx' : M i_target (Fin.natAdd r 0) = x := by simpa [hM_def] using hxx
  have hyy' : M i_target (Fin.natAdd r 1) = y := by simpa [hM_def] using hyy
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    matrix_mul_bezout2TrailingSL_apply x y hg M i_target hxx' hyy'
  refine ⟨?col0, ?cast, ?nat0, ?nat1, ?lin0, ?lin1⟩
  · -- (1) column 0 preserved.
    intro i
    exact slSuccEmbed_preserves_col_zero (bezout2TrailingSL r x y hg) N₀ i
  · -- (2) first `r` trailing columns preserved on every trailing row.
    intro i j
    have := h3 i j
    rw [hbridge i (Fin.castAdd 2 j)]
    simpa [hM_def] using this
  · -- (3) target trailing column 0 becomes `gcd`.
    rw [hbridge i_target (Fin.natAdd r 0)]; exact h1
  · -- (3') target trailing column 1 becomes `0`.
    rw [hbridge i_target (Fin.natAdd r 1)]; exact h2
  · -- (4) trailing column 0 linear combination on every trailing row.
    intro i
    have := h4 i
    rw [hbridge i (Fin.natAdd r 0)]
    simpa [hM_def] using this
  · -- (4') trailing column 1 linear combination on every trailing row.
    intro i
    have := h5 i
    rw [hbridge i (Fin.natAdd r 1)]
    simpa [hM_def] using this

/-- **Trailing-pair `SL₂(ℤ)` orthogonalizer.** For any integer pair `(x, y)`,
there exists `R ∈ SL_2(ℤ)` whose first column gives a ℤ-linear combination of
`(x, y)` equal to zero: `x * R.1 0 0 + y * R.1 1 0 = 0`. The construction is
`R := 1` for the degenerate case `(x, y) = (0, 0)`, and otherwise extends the
primitive pair `(y / g, -(x / g))` (where `g = Int.gcd x y > 0`) to an
`SL_2(ℤ)` matrix via `IsCoprime.exists_SL2_col`. This is the structural
content underlying the `k = 1` case of the trailing-block column-HNF
reduction. -/
private lemma exists_sl2_first_col_orthogonal (x y : ℤ) :
    ∃ R : SpecialLinearGroup (Fin 2) ℤ, x * R.1 0 0 + y * R.1 1 0 = 0 := by
  by_cases hxy : x = 0 ∧ y = 0
  · refine ⟨1, ?_⟩
    obtain ⟨hx, hy⟩ := hxy
    rw [hx, hy]; ring
  · push_neg at hxy
    have hg_pos_nat : 0 < Int.gcd x y := by
      rcases Nat.eq_zero_or_pos (Int.gcd x y) with h0 | hpos
      · rw [Int.gcd_eq_zero_iff] at h0
        exact absurd h0.2 (hxy h0.1)
      · exact hpos
    set g : ℤ := (Int.gcd x y : ℤ) with hg_def
    have hg_ne : g ≠ 0 := by
      show (Int.gcd x y : ℤ) ≠ 0
      exact_mod_cast hg_pos_nat.ne'
    have hg_dvd_x : g ∣ x := Int.gcd_dvd_left _ _
    have hg_dvd_y : g ∣ y := Int.gcd_dvd_right _ _
    obtain ⟨p, hxp⟩ := hg_dvd_x
    obtain ⟨q, hyq⟩ := hg_dvd_y
    have hpq_cop : Int.gcd p q = 1 := by
      have h1 : x / g = p := by rw [hxp]; exact Int.mul_ediv_cancel_left _ hg_ne
      have h2 : y / g = q := by rw [hyq]; exact Int.mul_ediv_cancel_left _ hg_ne
      have hkey := Int.gcd_div_gcd_div_gcd hg_pos_nat
      rw [h1, h2] at hkey
      exact hkey
    have hcop_pq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hpq_cop
    have hcop : IsCoprime q (-p) := hcop_pq.symm.neg_right
    obtain ⟨R, hR0, hR1⟩ := IsCoprime.exists_SL2_col hcop 0
    refine ⟨R, ?_⟩
    have h_R0 : R.1 0 0 = q := hR0
    have h_R1 : R.1 1 0 = -p := hR1
    rw [h_R0, h_R1, hxp, hyq]; ring

/-- **`k = 1` case of `sl_exists_col_stab_divChain`.**
The trailing block has size `2 × 2`, with a single divisibility constraint at
`(i, j) = (1, 0)`. Pick `N₀ : SL_3(ℤ)` extending `w` via
`sl_exists_col_of_primitive`; pick `R : SL_2(ℤ)` orthogonalizing the trailing
pair `(N₀.1 2 1, N₀.1 2 2)` via `exists_sl2_first_col_orthogonal`. The
trailing-block sum at `(1, 0)` then evaluates to `0`, which is divisible by
`(a 1 / a 0)`. The general `k ≥ 2` case (column-HNF iteration) is the remaining
content of `sl_exists_col_stab_divChain` and is left as a focused gap. -/
private lemma sl_exists_col_stab_divChain_one
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain 2 a)
    (w : Fin 3 → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin 2, (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin 3) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat 3 (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin 3) ℚ) *
        diagMat 3 (Fin.cons 1 a) ∈ (GL_pair 3).H := by
  refine sl_exists_col_stab_divChain_of_trailing_hnf_data a ha hda w hw_col_div ?_
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive (n := 1) w hw_primitive
  obtain ⟨R, hR_eq⟩ :=
    exists_sl2_first_col_orthogonal (N₀.1 2 1) (N₀.1 2 2)
  refine ⟨N₀, R, hcol₀, ?_⟩
  intro i j hji
  have hi_one : i = 1 := by
    fin_cases i
    · exact absurd hji (Fin.not_lt_zero _)
    · rfl
  subst hi_one
  have hj_zero : j = 0 := by
    fin_cases j
    · rfl
    · exact absurd hji (lt_irrefl _)
  subst hj_zero
  have h_sum : ∑ k' : Fin 2, N₀.1 ((1 : Fin 2).succ) k'.succ * R.1 k' 0 =
      N₀.1 2 1 * R.1 0 0 + N₀.1 2 2 * R.1 1 0 := by
    rw [Fin.sum_univ_two]; rfl
  rw [h_sum, hR_eq]
  exact dvd_zero _

/-- **Existence of a non-zero kernel vector via rank-nullity.**  Any
`(m + 1) × (m + 2)` integer matrix `N` has a non-zero integer vector in its
right kernel (column-vector orientation): there exists `v : Fin (m + 2) → ℤ`
with `v ≠ 0` and `∀ i, ∑ j, N i j * v j = 0`.

Proof:  view `N` as the linear map `N.mulVecLin : ℤ^{m+2} → ℤ^{m+1}`.  If its
kernel were `⊥`, the map would be injective, forcing
`finrank ℤ (Fin (m + 2) → ℤ) ≤ finrank ℤ (Fin (m + 1) → ℤ)` via
`LinearMap.finrank_le_finrank_of_injective`, i.e. `m + 2 ≤ m + 1`, a
contradiction.  Hence the kernel is non-`⊥`; `Submodule.exists_mem_ne_zero_of_ne_bot`
extracts a non-zero element, and translation through `Matrix.mulVecLin_apply` /
`Matrix.mulVec` yields the component-wise sum equation. -/
private lemma exists_nonzero_kernel_vec {m : ℕ}
    (N : Matrix (Fin (m + 1)) (Fin (m + 2)) ℤ) :
    ∃ v : Fin (m + 2) → ℤ,
      v ≠ 0 ∧ (∀ i : Fin (m + 1), ∑ j, N i j * v j = 0) := by
  let L : (Fin (m + 2) → ℤ) →ₗ[ℤ] (Fin (m + 1) → ℤ) := N.mulVecLin
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hbot
    have h_le : Module.finrank ℤ (Fin (m + 2) → ℤ) ≤
        Module.finrank ℤ (Fin (m + 1) → ℤ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h_le
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨v, hv_ne, ?_⟩
  intro i
  have h_Lv : L v = 0 := LinearMap.mem_ker.mp hv_mem
  have h_app : (N *ᵥ v) i = (0 : Fin (m + 1) → ℤ) i := by
    show (L v) i = (0 : Fin (m + 1) → ℤ) i
    exact congrFun h_Lv i
  simpa [Matrix.mulVec, dotProduct] using h_app

/-- **Primitive-kernel-vector lemma.**  Any `(m + 1) × (m + 2)` integer matrix
`N` has a primitive integer vector in its right kernel.  Proven by composing
`exists_nonzero_kernel_vec` (a non-zero kernel vector) with a gcd-normalisation
step:  divide each entry by the gcd of all entries to obtain a primitive vector
that is still in the kernel (since the kernel of a linear map between free
`ℤ`-modules is closed under integer division when the result is integer). -/
private lemma exists_primitive_kernel_vec {m : ℕ}
    (N : Matrix (Fin (m + 1)) (Fin (m + 2)) ℤ) :
    ∃ v : Fin (m + 2) → ℤ,
      (∀ d : ℤ, (∀ i, d ∣ v i) → IsUnit d) ∧
      (∀ i : Fin (m + 1), ∑ j, N i j * v j = 0) := by
  obtain ⟨v, hv_ne, hv_kernel⟩ := exists_nonzero_kernel_vec N
  set g : ℤ := Finset.univ.gcd v with hg_def
  have hg_dvd : ∀ j, g ∣ v j := fun j ↦ Finset.gcd_dvd (Finset.mem_univ j)
  have hg_ne_zero : g ≠ 0 := by
    intro hg0
    apply hv_ne
    funext j
    have hgvj : g ∣ v j := hg_dvd j
    rw [hg0] at hgvj
    exact zero_dvd_iff.mp hgvj
  refine ⟨fun j ↦ v j / g, ?_, ?_⟩
  · -- Primitivity:  any common divisor `d` of `v j / g` satisfies `d * g ∣ g`,
    intro d hd
    have hdg_dvd_v : ∀ j, d * g ∣ v j := by
      intro j
      have hvj_eq : v j = g * (v j / g) := (Int.mul_ediv_cancel' (hg_dvd j)).symm
      rw [hvj_eq, mul_comm d g]
      exact mul_dvd_mul_left g (hd j)
    have hdg_dvd_g : d * g ∣ g :=
      Finset.dvd_gcd (fun j _ ↦ hdg_dvd_v j)
    have hd_dvd_one : d ∣ 1 := by
      have hone : d * g ∣ 1 * g := by rwa [one_mul]
      exact (mul_dvd_mul_iff_right hg_ne_zero).mp hone
    exact isUnit_of_dvd_one hd_dvd_one
  · -- Kernel:  multiply by `g` to reduce to the original kernel relation.
    intro i
    show ∑ j : Fin (m + 2), N i j * (v j / g) = 0
    have hLHS_g :
        g * (∑ j, N i j * (v j / g)) = 0 := by
      rw [Finset.mul_sum]
      have h_term : ∀ j ∈ (Finset.univ : Finset (Fin (m + 2))),
          g * (N i j * (v j / g)) = N i j * v j := by
        intro j _
        have h_cancel : g * (v j / g) = v j := Int.mul_ediv_cancel' (hg_dvd j)
        calc g * (N i j * (v j / g))
            = N i j * (g * (v j / g)) := by ring
          _ = N i j * v j := by rw [h_cancel]
      rw [Finset.sum_congr rfl h_term]
      exact hv_kernel i
    have h_eq : g * (∑ j, N i j * (v j / g)) = g * 0 := by rw [mul_zero]; exact hLHS_g
    exact mul_left_cancel₀ hg_ne_zero h_eq

/-- **Single-column clearing for the column-HNF inductive step.**  For any
`(n + 2) × (n + 2)` integer matrix `M`, there exists `R ∈ SL_(n+2)(ℤ)` such
that the first column of `M * R` has zero in every row below row 0, i.e.,
`(M * R)[i.succ][0] = 0` for all `i : Fin (n + 1)`.

Proven from the strictly-smaller `exists_primitive_kernel_vec` blocker:
extract a primitive vector `v` in the right kernel of `M`'s rows `1, …, n + 1`,
then use `sl_exists_col_of_primitive` to lift `v` to an `SL_(n+2)(ℤ)` matrix
whose first column equals `v`.  The kernel-vector condition then exactly
matches `(M * R)[i.succ][0] = 0`. -/
private lemma exists_sl_clear_col_zero {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ) :
    ∃ R : SpecialLinearGroup (Fin (n + 2)) ℤ,
      ∀ i : Fin (n + 1), (M * R.val) i.succ 0 = 0 := by
  obtain ⟨v, hv_prim, hv_kernel⟩ :=
    exists_primitive_kernel_vec (fun (i : Fin (n + 1)) (j : Fin (n + 2)) ↦ M i.succ j)
  obtain ⟨R, hR⟩ := sl_exists_col_of_primitive v hv_prim
  refine ⟨R, ?_⟩
  intro i
  rw [Matrix.mul_apply]
  have h_sum_eq :
      ∑ k : Fin (n + 2), M i.succ k * R.val k 0 =
      ∑ k : Fin (n + 2), M i.succ k * v k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hR k]
  rw [h_sum_eq]
  exact hv_kernel i

/-- **Trailing-block column upper-triangularization (general dim).**  For any
`n × n` integer matrix `M`, there exists `R ∈ SL_n(ℤ)` such that the
strict-lower entries of `M * R` are zero (i.e., `M * R` is upper triangular).
This is the column-HNF iteration for arbitrary square integer matrices.

Fully proven via:  the trivial cases `n ≤ 1` (vacuous constraint), the
`n = 2` base case (via `exists_sl2_first_col_orthogonal`), and an inductive
step for `n + 3` that combines `exists_sl_clear_col_zero` (clears column 0
below row 0) with the recursive IH applied to the `(n + 2) × (n + 2)` trailing
submatrix below row 0 / column 0, embedded back via `slSuccEmbed`.  The
single-column clearer is itself proven from the strictly-smaller
`exists_primitive_kernel_vec`, which is the only remaining algebraic blocker. -/
private lemma sl_upperTri_for_matrix : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ),
    ∃ R : SpecialLinearGroup (Fin n) ℤ,
      ∀ i j : Fin n, j < i → (M * R.val) i j = 0
  | 0, _M => ⟨1, fun i _ _ ↦ i.elim0⟩
  | 1, _M => ⟨1, by
      intro i j hji
      have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      have : ¬ j < i := by
        rw [Fin.lt_def, hi, hj]; exact lt_irrefl _
      exact absurd hji this⟩
  | 2, M => by
      obtain ⟨R, hR⟩ := exists_sl2_first_col_orthogonal (M 1 0) (M 1 1)
      refine ⟨R, ?_⟩
      intro i j hji
      have hi : i = 1 := by
        fin_cases i
        · exact absurd hji (Fin.not_lt_zero _)
        · rfl
      subst hi
      have hj : j = 0 := by
        fin_cases j
        · rfl
        · exact absurd hji (lt_irrefl _)
      subst hj
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact hR
  | n + 3, M => by
      obtain ⟨R₁, hR₁⟩ := exists_sl_clear_col_zero M
      let Mtail : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
        fun i k' ↦ (M * R₁.val) i.succ k'.succ
      obtain ⟨R', hR'⟩ := sl_upperTri_for_matrix Mtail
      refine ⟨R₁ * slSuccEmbed R', ?_⟩
      intro i j hji
      show (M * (R₁ * slSuccEmbed R').val) i j = 0
      rw [SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
      · -- `i = 0`:  vacuous (`j < 0` impossible).
        subst hi; exact absurd hji (Fin.not_lt_zero _)
      · subst hi
        rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
        · -- `j = 0`:  goal reduces to `(M * R₁.val) i'.succ 0 = 0`.
          subst hj
          simp only [slSuccEmbed_val_zero_zero, mul_one, slSuccEmbed_val_succ_zero,
            mul_zero, Finset.sum_const_zero, add_zero]
          exact hR₁ i'
        · -- `j = j'.succ`:  goal reduces to `(Mtail * R'.val) i' j' = 0` via IH.
          subst hj
          simp only [slSuccEmbed_val_zero_succ, mul_zero, zero_add,
            slSuccEmbed_val_succ_succ]
          have hji_sub : j' < i' := by
            have h1 : j'.succ.val < i'.succ.val := hji
            simp only [Fin.val_succ] at h1
            exact Fin.lt_def.mpr (by omega)
          have h_sum_eq :
              ∑ k' : Fin (n + 2),
                (M * R₁.val) i'.succ k'.succ * R'.val k' j' =
              (Mtail * R'.val) i' j' := by
            rw [Matrix.mul_apply]
          rw [h_sum_eq, hR' i' j' hji_sub]

/-- **Primitive vector completion with DivChain-respecting stabilizer
membership** — the isolated combinatorial core behind
`fiber_has_block_form_preimages`. Given a primitive integer vector
`w : Fin (k+2) → ℤ` whose entries satisfy the DivChain-forced column-0
divisibility `a_{i-1} ∣ w_{i.succ}`, there exists `N ∈ SL_{k+2}(ℤ)` with
first column `w` and with `N` in the stabilizer of `diagMat (Fin.cons 1 a)`
(equivalently: the lower-triangular entries of `N` satisfy the
`a_{i-1}/a_{j-1}` divisibility for `i > j > 0`). The proof is a classical
Smith-normal-form / column-by-column Bezout construction; it does not depend
on the specific Shimura fiber context. -/
private lemma sl_exists_col_stab_divChain {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  rcases k with _ | _ | k
  · exact sl_exists_col_stab_divChain_zero a ha hda w hw_primitive hw_col_div
  · exact sl_exists_col_stab_divChain_one a ha hda w hw_primitive hw_col_div
  · -- k + 2 case: build a TrailingBlockHNFData via `sl_upperTri_for_matrix`.
    refine sl_exists_col_stab_divChain_of_trailing_hnf_data a ha hda w hw_col_div ?_
    obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
    let Mtail : Matrix (Fin (k + 3)) (Fin (k + 3)) ℤ :=
      fun i k' ↦ N₀.1 i.succ k'.succ
    obtain ⟨R, hR⟩ := sl_upperTri_for_matrix Mtail
    refine ⟨N₀, R, hcol₀, ?_⟩
    intro i j hji
    have h_sum :
        ∑ k' : Fin (k + 3), N₀.1 i.succ k'.succ * R.val k' j =
        (Mtail * R.val) i j := by
      rw [Matrix.mul_apply]
    rw [h_sum, hR i j hji]
    exact dvd_zero _

/-- **Sorry-free translation helper for the dim-`(k+2)` stabilizer subgroup.**
Membership of `σ : (GL_pair (k+2)).H` in the abstract `subgroupOf`-style
stabilizer for `diagMat_delta (k+2) (Fin.cons 1 a)` is equivalent to the concrete
matrix-conjugation condition `D⁻¹ * σ * D ∈ (GL_pair (k+2)).H` (where
`D = diagMat (k+2) (Fin.cons 1 a)`).  This bridges the `decompQuot` quotient
representation (used by `fiber_has_block_form_preimages` in its hypothesis
on `i.out`, `j.out`) and the matrix-conjugation form consumed by
`slSuccEmbed_H_fiber_transfer` and `slSuccEmbed_H_stab_diagMat`.  The proof is
just unfolding `Subgroup.mem_subgroupOf` and the pointwise smul / `ConjAct`
definitions, then identifying the two diagonal forms via `diagMat_delta_val`. -/
private lemma mem_diagMat_cons_stabilizer_subgroupOf_iff {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (σ : (GL_pair (k + 2)).H) :
    σ ∈ (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) :
            (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf
          (GL_pair (k + 2)).H ↔
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)]

/-- **Integer-level conjugation identity for a `Fin.cons 1 _`-stabilizer SL matrix.**
Given `M : SL_(k+2)(ℤ)` whose `mapGL ℚ`-image lies in the diag-conjugation stabilizer of
`Fin.cons 1 a` (i.e., `D⁻¹ * mapGL ℚ M * D ∈ (GL_pair (k+2)).H` where
`D = diagMat (k+2) (Fin.cons 1 a)`), there exists an integer SL matrix `N : SL_(k+2)(ℤ)`
satisfying the integer-matrix identity
`Matrix.diagonal (Fin.cons 1 a · ↑) * N.val = M.val * Matrix.diagonal (Fin.cons 1 a · ↑)`.

This is the integer-level translation of the stabilizer condition: the GL-conjugation
`D⁻¹ * (mapGL ℚ M) * D = mapGL ℚ N` is equivalent to `D * mapGL ℚ N = mapGL ℚ M * D` in
`GL (Fin (k+2)) ℚ`, which descends to an integer-matrix identity `D · N = M · D` (no
rational `D⁻¹` factor). It is the natural input for any subsequent algebraic substitution
of the i-side / j-side block-form factor `M` into the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` produced by `hfib_int_mat_eq`, since the stab condition
on `M` lets us replace `M⁻¹ · D_a` by `D_a · N⁻¹` (a corollary at integer level via
`M⁻¹ · D = D · N⁻¹` from this identity).

Reusable helper for any future j-side or coordinated rep-construction work that needs
to rewrite a stab-conjugated factor as a left- or right-diagonal-times-integer-SL form. -/
private lemma exists_stab_int_conjugate_diagMat_cons_one {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hM_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ)) * N.val =
        M.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ)) := by
  obtain ⟨N, hN⟩ := hM_stab
  refine ⟨N, ?_⟩
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  have h_GL_eq : diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_mat := congr_arg
    (fun g : GL (Fin (k + 2)) ℚ ↦ (g : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)) h_GL_eq
  simp only [Units.val_mul] at h_mat
  have h_N : ((mapGL ℚ N : GL _ ℚ) : Matrix _ _ ℚ) = N.1.map (algebraMap ℤ ℚ) := rfl
  have h_M : ((mapGL ℚ M : GL _ ℚ) : Matrix _ _ ℚ) = M.1.map (algebraMap ℤ ℚ) := rfl
  have h_D : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_pos,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [h_N, h_M, h_D] at h_mat
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h_mat
  exact (Matrix.map_injective (algebraMap ℤ ℚ).injective_int h_mat)

/-- **Sorry-free first-column divisibility extraction from the `Fin.cons 1 _`
stabilizer condition.**  If `σ : (GL_pair (k+2)).H` lies in the
`subgroupOf`-style stabilizer for `diagMat_delta (k+2) (Fin.cons 1 a)`, then the
underlying integer matrix `toSL σ` has its first column entries (below row 0)
divisible by the chain `a` — concretely, `a i ∣ (toSL σ) (i.succ) 0` for every
`i : Fin (k+1)`.  This is exactly the `hw_col_div` hypothesis required by
`sl_exists_col_stab_divChain`, so combining this lemma with
`mem_diagMat_cons_stabilizer_subgroupOf_iff` lets a stabilizer-element `σ`
feed directly into the SL-stabilizer-existence machinery used by the
column-HNF iteration.

Proof:  `mem_diagMat_cons_stabilizer_subgroupOf_iff` rewrites the abstract
membership to `D⁻¹ * σ * D ∈ (GL_pair (k+2)).H`, hence equal to `mapGL ℚ N`
for some `N : SL_(k+2)(ℤ)`.  Multiplying by `D` on the left gives the matrix
identity `D * mapGL N = σ * D`; reading off the `(i.succ, 0)` entry uses the
diagonal structure of `D` to collapse the sums to
`(a i : ℚ) * (N.val (i.succ) 0 : ℚ) = ((toSL σ).val (i.succ) 0 : ℚ)`, after
which integer divisibility is `exact_mod_cast`. -/
private lemma stabilizer_implies_first_col_div_chain {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 2)).H)
    (hσ_stab : σ ∈ (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) :
            (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf
          (GL_pair (k + 2)).H) :
    ∀ i : Fin (k + 1), (a i : ℤ) ∣ (toSL σ).val i.succ 0 := by
  rw [mem_diagMat_cons_stabilizer_subgroupOf_iff a ha] at hσ_stab
  obtain ⟨N, hN⟩ := hσ_stab
  intro i
  refine ⟨N.val i.succ 0, ?_⟩
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  have h_GL_eq :
      diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N) =
      (σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_entry :
      ((diagMat (k + 2) (Fin.cons 1 a)).val *
        (mapGL ℚ N).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) i.succ 0 =
      ((σ : GL (Fin (k + 2)) ℚ).val *
        (diagMat (k + 2) (Fin.cons 1 a)).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)
          i.succ 0 := by
    have h_units := congr_arg Units.val h_GL_eq
    simp only [Units.val_mul] at h_units
    exact congrFun (congrFun h_units i.succ) 0
  rw [diagMat_val _ _ hcons_pos, Matrix.diagonal_mul, Matrix.mul_diagonal] at h_entry
  have hcons_succ : ((Fin.cons 1 a : Fin (k + 2) → ℕ) i.succ : ℚ) = (a i : ℚ) := by
    simp [Fin.cons_succ]
  have hcons_zero : ((Fin.cons 1 a : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℚ) = 1 := by
    simp [Fin.cons_zero]
  rw [hcons_succ, hcons_zero, mul_one, mapGL_coe_matrix] at h_entry
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_int_eq, eq_intCast] at h_entry
  have h_toSL_val :
      ((toSL σ).val i.succ 0 : ℚ) = (σ : GL (Fin (k + 2)) ℚ).val i.succ 0 := by
    have h_units := congr_arg Units.val (toSL_spec σ)
    rw [mapGL_coe_matrix] at h_units
    have := congrFun (congrFun h_units i.succ) 0
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, algebraMap_int_eq, eq_intCast] at this
    exact this
  rw [← h_toSL_val] at h_entry
  exact_mod_cast h_entry.symm

/-- **Sorry-free `i`-side stabilizer SL matrix from the fiber relation.**
Given the fiber condition `hfib` and a positive divisor chain `a` (`hda`), the
chain-divisibility of `(toSL i.out)⁻¹`'s first column (provided by
`hfib_col_div_a`) plus its primitivity (provided by `sl_first_col_primitive`,
since `(toSL i.out)⁻¹ ∈ SL_(k+2)(ℤ)`) feeds directly into
`sl_exists_col_stab_divChain` to produce an `M : SL_(k+2)(ℤ)` satisfying:
  * `M.1 r 0 = ((toSL i.out)⁻¹).1 r 0` for every `r : Fin (k + 2)` — `M`'s
    first column matches the inverse-column we want to absorb;
  * `D⁻¹ * mapGL ℚ M * D ∈ (GL_pair (k+2)).H` — `M` lies in the
    `Fin.cons 1 a` diagonal-conjugation stabilizer.

This is the right-multiplication factor for the i-side block-form
decomposition: `(toSL i.out) * M` has first column equal to
`(toSL i.out) * ((toSL i.out)⁻¹).1 _ 0 = e_0`, the first step of the block
form `1 ⊕ σ_m`.  Sorry-free because every input has been previously closed. -/
private lemma exists_stab_with_inv_first_col_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ M : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2), M.1 r 0 = ((toSL i.out)⁻¹ :
        SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  have h_div := hfib_col_div_a a b c ha hb hc i j hfib
  set w : Fin (k + 2) → ℤ :=
    fun r ↦ ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 with hw_def
  have hw_primitive : ∀ d : ℤ, (∀ r, d ∣ w r) → IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (toSL i.out)⁻¹ d hd
  have hw_col_div : ∀ i' : Fin (k + 1), (a i' : ℤ) ∣ w i'.succ := h_div
  exact sl_exists_col_stab_divChain a ha hda w hw_primitive hw_col_div

/-- **First-column-`e_0` reduction of `i.out` from the fiber relation.**  Given
the fiber condition `hfib`, there exists a stabilizer SL matrix `M` (built from
`exists_stab_with_inv_first_col_of_fiber`) such that `(toSL i.out) * M` has
first column equal to `e_0` (i.e., the first column of the identity matrix):
`(toSL i.out * M).1 r 0 = (1 : Matrix _ _ ℤ) r 0` for every `r : Fin (k + 2)`.

Direct computation: `M`'s first column matches `(toSL i.out)⁻¹`'s first
column, so `(toSL i.out * M)`'s first column equals
`(toSL i.out * (toSL i.out)⁻¹)`'s first column = `(1 : SL).1`'s first
column = the first standard basis vector.  This is the second step of the
i-side block-form decomposition (after the stabilizer-extraction step
`exists_stab_with_inv_first_col_of_fiber`); the next step is clearing the
first row of `toSL i.out * M` by upper transvections (which are automatically
in the stabilizer, since their only non-identity entry sits in the
strict-upper triangle). -/
private lemma exists_stab_with_first_col_e0_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ M : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2),
        (toSL i.out * M : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 =
          (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M, hM_col, hM_stab⟩ :=
    exists_stab_with_inv_first_col_of_fiber a b c ha hb hc hda i j hfib
  refine ⟨M, ?_, hM_stab⟩
  intro r
  have h_to_inv :
      (toSL i.out * M : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 =
      (toSL i.out * (toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 := by
    simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [hM_col k]
  rw [h_to_inv, mul_inv_cancel, SpecialLinearGroup.coe_one]

/-- **Transvection at `(0, l.succ)` lies in the diag-conjugation stabilizer**
for diagonals of the form `Fin.cons 1 a`. Conjugation by `diag` sends a
transvection with donor row `0` to another integer transvection (the constant
`c` is multiplied by `a_l`), so the conjugate is automatically in
`SLnZ_subgroup`. This is the "upper-row transvection stays integer" fact used
when clearing the first row of a matrix that already has first column equal to
the first standard basis vector. -/
private lemma slTransvec_zero_succ_stab {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (l : Fin (k + 1)) (c : ℤ) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ (slTransvecG (0 : Fin (k + 2)) l.succ (Fin.succ_ne_zero l).symm c)
        : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  apply diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd a ha
  intro i' j'
  by_cases hi : i' = 0
  · -- (cons 1 a) 0 = 1, so the LHS divisor is 1.
    subst hi
    show ((Fin.cons 1 a : Fin (k + 2) → ℕ) 0 : ℤ) ∣ _
    simp
  · -- i' ≠ 0: the c contribution at entry (i', j') vanishes (it requires `0 = i'`).
    have h_no_c : ¬ (0 = i' ∧ l.succ = j') := fun ⟨h0, _⟩ ↦ hi h0.symm
    have h_entry :
        (slTransvecG (0 : Fin (k + 2)) l.succ (Fin.succ_ne_zero l).symm c).1 i' j' =
          if i' = j' then 1 else 0 := by
      show (Matrix.transvection (0 : Fin (k + 2)) l.succ c) i' j' = _
      simp [Matrix.transvection, Matrix.one_apply, h_no_c]
    rw [h_entry]
    by_cases h_diag : i' = j'
    · subst h_diag
      simp
    · simp [h_diag]

/-- **Row-clearance via upper transvections** with stabilizer membership.
Given a matrix `W ∈ SL(k+2, ℤ)` whose first column equals `e₀` and a finset
`S : Finset (Fin (k+1))` of "columns to clear", produce a transvection product
`T ∈ SL(k+2, ℤ)` such that `W * T` keeps column `0` fixed, zeroes the
`(0, l.succ)` entry for every `l ∈ S`, leaves other first-row entries
unchanged, leaves the bottom-right `(k+1) × (k+1)` block unchanged, and
satisfies the diag-conjugation stabilizer condition. The proof inducts on `S`
using `slTransvec_zero_succ_stab` for stabilizer closure. -/
private lemma sl_first_row_clear_with_col0_e0 {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (W : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col0 : ∀ r : Fin (k + 2),
      W.1 r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0)
    (S : Finset (Fin (k + 1))) :
    ∃ T : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2), (W * T).1 r 0 = W.1 r 0) ∧
      (∀ l : Fin (k + 1), l ∈ S → (W * T).1 0 l.succ = 0) ∧
      (∀ l : Fin (k + 1), l ∉ S → (W * T).1 0 l.succ = W.1 0 l.succ) ∧
      (∀ i j : Fin (k + 1), (W * T).1 i.succ j.succ = W.1 i.succ j.succ) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ T : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  have h_col0_zero : W.1 0 0 = 1 := by
    have h := h_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have h_col0_succ_zero : ∀ r' : Fin (k + 1), W.1 r'.succ 0 = 0 := by
    intro r'
    have h := h_col0 r'.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero r')] at h
    exact h
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩
      · intro r; simp
      · intro l hl; exact absurd hl (Finset.notMem_empty _)
      · intro l _; simp
      · intro i j; simp
      · -- 1 conjugated by anything is 1, in H trivially
        show (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ (1 : SpecialLinearGroup (Fin (k + 2)) ℤ) : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H
        rw [map_one, mul_one, inv_mul_cancel]
        exact one_mem _
  | insert l₀ S' hl₀_notin ih =>
      obtain ⟨T', hT'_col0, hT'_S, hT'_outside, hT'_block, hT'_stab⟩ := ih
      set c_l₀ : ℤ := -(W.1 0 l₀.succ) with hc_l₀_def
      set T_l₀ : SpecialLinearGroup (Fin (k + 2)) ℤ :=
        slTransvecG (0 : Fin (k + 2)) l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ with hT_l₀_def
      have h_WT'_00 : (W * T').1 0 0 = 1 := by rw [hT'_col0 0]; exact h_col0_zero
      refine ⟨T' * T_l₀, ?_, ?_, ?_, ?_, ?_⟩
      · -- column 0 still W's column 0
        intro r
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def,
          sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') r
              (Fin.succ_ne_zero l₀).symm]
        exact hT'_col0 r
      · -- Columns in `insert l₀ S'` are cleared.
        intro l hl
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        obtain h_eq | hl_S' := Finset.mem_insert.mp hl
        · -- After `subst h_eq` (h_eq : l = l₀), `l₀` is replaced by `l` everywhere.
          subst h_eq
          rw [sl_addCol_target_col 0 l.succ (Fin.succ_ne_zero l).symm c_l₀ (W * T') 0,
            hT'_outside l hl₀_notin, h_WT'_00]
          show W.1 0 l.succ + c_l₀ * 1 = 0
          rw [hc_l₀_def]; ring
        · have hl_ne_l₀ : l ≠ l₀ := fun h ↦ hl₀_notin (h ▸ hl_S')
          have hsucc_ne : l.succ ≠ l₀.succ := fun h ↦ hl_ne_l₀ (Fin.succ_injective _ h)
          rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
              hsucc_ne]
          exact hT'_S l hl_S'
      · intro l hl_notin
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        have hl_ne_l₀ : l ≠ l₀ := fun h ↦ hl_notin (h ▸ Finset.mem_insert_self _ _)
        have hl_notin_S' : l ∉ S' := fun h ↦ hl_notin (Finset.mem_insert_of_mem h)
        have hsucc_ne : l.succ ≠ l₀.succ := fun h ↦ hl_ne_l₀ (Fin.succ_injective _ h)
        rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
            hsucc_ne]
        exact hT'_outside l hl_notin_S'
      · intro i' j'
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        by_cases h_eq : j'.succ = l₀.succ
        · -- j'.succ = l₀.succ → j' = l₀ by injectivity, substitute first.
          have hj'_eq : j' = l₀ := Fin.succ_injective _ h_eq
          subst hj'_eq
          rw [sl_addCol_target_col 0 j'.succ (Fin.succ_ne_zero j').symm c_l₀ (W * T') i'.succ]
          have hcol0_succ : (W * T').1 i'.succ 0 = 0 := by
            rw [hT'_col0 i'.succ]; exact h_col0_succ_zero i'
          rw [hcol0_succ, mul_zero, add_zero]
          exact hT'_block i' j'
        · rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') i'.succ
              h_eq]
          exact hT'_block i' j'
      · -- Stabilizer: factor through map_mul.
        have h_T_l₀_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
            (mapGL ℚ T_l₀ : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
          rw [hT_l₀_def]
          exact slTransvec_zero_succ_stab a ha l₀ c_l₀
        have h_split : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
            (mapGL ℚ (T' * T_l₀) : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) =
            ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
              (mapGL ℚ T' : GL (Fin (k + 2)) ℚ) *
              diagMat (k + 2) (Fin.cons 1 a)) *
            ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
              (mapGL ℚ T_l₀ : GL (Fin (k + 2)) ℚ) *
              diagMat (k + 2) (Fin.cons 1 a)) := by
          rw [map_mul]; group
        rw [h_split]
        exact mul_mem hT'_stab h_T_l₀_stab

/-- **i-side block-form witness from the fiber.** Combining
`exists_stab_with_first_col_e0_of_fiber` with `sl_first_row_clear_with_col0_e0`,
produce `M ∈ SL(k+2, ℤ)` in the diag-conjugation stabilizer and
`σ_m ∈ SL(k+1, ℤ)` such that `toSL i.out * M = slSuccEmbed σ_m`. This is the
i-side bridge: it identifies `i.out` (modulo stabilizer) with the
block-embedding image of a dim-(k+1) class. -/
private lemma exists_stab_with_block_form_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL i.out * M = slSuccEmbed σ_m ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M_0, hM_0_col, hM_0_stab⟩ :=
    exists_stab_with_first_col_e0_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 a ha (toSL i.out * M_0) hM_0_col Finset.univ
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0 * T_clear with hM_def
  set N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (toSL i.out * M).1 with hN_def
  have hM_assoc : toSL i.out * M = (toSL i.out * M_0) * T_clear := by
    rw [hM_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (toSL i.out * M).1 r 0 = _
    rw [hM_assoc, hT_col0 r]
    exact hM_0_col r
  have hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0 := by
    intro l
    show (toSL i.out * M).1 0 l.succ = _
    rw [hM_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set σ_m_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N I.succ J.succ with hσ_raw_def
  have h_det : σ_m_raw.det = 1 := by
    have h_det_N : N.det = 1 := by
      rw [hN_def]; exact (toSL i.out * M).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N 0 j.succ *
            (N.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = σ_m_raw := by
      ext I J
      show N I.succ ((0 : Fin (k + 2)).succAbove J) = σ_m_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨σ_m_raw, h_det⟩ with hσ_def
  refine ⟨M, σ_m, ?_, ?_⟩
  · apply Subtype.ext
    ext I J
    show N I J = (slSuccEmbed σ_m).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · -- (0, 0)
        rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  · -- Stabilizer: M = M_0 * T_clear, both in stabilizer.
    have h_split : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_0 : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a)) *
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a)) := by
      rw [hM_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_stab hT_stab

/-- **Substituted integer matrix equation via the i-side block form, EXPLICIT-input form.**

Same algebraic content as `fiber_int_mat_eq_via_i_block` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, h_block_i, N_i, h_int_conj)`.
Returns just the substituted integer matrix equation
`block(σ_i) · D_a · (N_i⁻¹ · A_j) · D_b = D_c · ν`, where `A_j := toSL j.out`
and `block(σ_i) := slSuccEmbed σ_i`.

**Why the explicit-input form.**  When the caller supplies `(M_i, σ_i, N_i)`
extracted via `Classical.choose` on the **i-only** existentials
`exists_stab_with_block_form_of_fiber` and `exists_stab_int_conjugate_diagMat_cons_one`
(both with i-only existential bodies), Lean 4's proof irrelevance makes those
witnesses i-functional (independent of `(j, hfib)`).  The combined j-dependent
output of `fiber_int_mat_eq_via_i_block` (which packages all four witnesses
σ_i, M_i, N_i, ν into a single existential whose body has j-dependent
conjuncts) does **not** preserve i-functionality through `Classical.choose`,
which is the architectural blocker to closing
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`'s
`h_iFunctional` hypothesis.  Threading explicit i-functional witnesses
through this lemma (and the downstream chain) keeps i-functionality intact.

**Use site.**  Together with the (planned) explicit-input variants of
`_rearr`, `_rearr_adj`, `hfib_col_div_b_via_i_block`,
`fiber_block_form_preimage_corrected_j`, and `_mulMap`, this gives a
parameterized chain whose final mulMap output's `N_i` matches the caller's
i-functional `N_i`. -/
private lemma fiber_int_mat_eq_via_i_block_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (slSuccEmbed σ_i).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (N_i⁻¹ * toSL j.out).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.val := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  have h_M_inv_M_val :
      (M_i⁻¹).val * M_i.val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    show ((M_i⁻¹) * M_i).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val
    rw [inv_mul_cancel]
  have h_N_N_inv_val :
      N_i.val * (N_i⁻¹).val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    show (N_i * N_i⁻¹).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val
    rw [mul_inv_cancel]
  have h_inv_conj : (M_i⁻¹).val * D_a = D_a * (N_i⁻¹).val := by
    have step1 : (M_i⁻¹).val * D_a * N_i.val = D_a := by
      rw [Matrix.mul_assoc, h_int_conj, ← Matrix.mul_assoc, h_M_inv_M_val,
          Matrix.one_mul]
    have step2 :
        (M_i⁻¹).val * D_a * N_i.val * (N_i⁻¹).val = D_a * (N_i⁻¹).val := by
      rw [step1]
    rw [Matrix.mul_assoc, h_N_N_inv_val, Matrix.mul_one] at step2
    exact step2
  have h_block_i_inv : toSL i.out = slSuccEmbed σ_i * M_i⁻¹ := by
    rw [← h_block_i, mul_inv_cancel_right]
  have h_block_i_inv_val : (toSL i.out).val =
      (slSuccEmbed σ_i).val * (M_i⁻¹).val := by
    show ((toSL i.out)).val = ((slSuccEmbed σ_i) * M_i⁻¹).val
    rw [← h_block_i_inv]
  have h_unfold_prod : (N_i⁻¹ * toSL j.out).val =
      (N_i⁻¹).val * (toSL j.out).val := rfl
  rw [h_unfold_prod]
  rw [show (slSuccEmbed σ_i).val * D_a * ((N_i⁻¹).val * (toSL j.out).val) * D_b =
      ((slSuccEmbed σ_i).val * (D_a * (N_i⁻¹).val)) * (toSL j.out).val * D_b from by
    simp only [Matrix.mul_assoc]]
  rw [← h_inv_conj]
  rw [show (slSuccEmbed σ_i).val * ((M_i⁻¹).val * D_a) * (toSL j.out).val * D_b =
      ((slSuccEmbed σ_i).val * (M_i⁻¹).val) * D_a * (toSL j.out).val * D_b from by
    simp only [← Matrix.mul_assoc]]
  rw [← h_block_i_inv_val]
  exact hν

/-- **Substituted integer matrix equation via the i-side block form.**
Combines `exists_stab_with_block_form_of_fiber` (i-side block form),
`exists_stab_int_conjugate_diagMat_cons_one` (integer conjugation
identity), and `hfib_int_mat_eq` (raw integer matrix equation) into a
single packaging that produces:

* the i-side block witnesses `M_i, σ_i` with `toSL i.out * M_i =
  slSuccEmbed σ_i` and `M_i ∈ stab(D_a)`;
* the integer conjugate `N_i` with `D_a · N_i = M_i · D_a`;
* the matrix-equation witness `ν` with the substituted equation
  `block(σ_i) · D_a · (N_i⁻¹ · A_j) · D_b = D_c · ν`,
  where `A_j := toSL j.out` and `block(σ_i) := slSuccEmbed σ_i`.

This is the natural setup for any future j-side block-form construction
(or a coordinated Smith-NF / lattice-descent producing both block witnesses
together): the i-side has been absorbed into the `slSuccEmbed σ_i` factor
on the left, so the j-side construction need only operate on the rest of
the equation. The `N_i⁻¹ · A_j` factor in the substituted equation is the
SL element whose first column controls the j-side col-divisibility
question (the exact next missing arithmetic input — see the docstring at
`fiber_has_block_form_preimages` for the dim-2 counterexample at k = 0
showing the canonical j-side col-divisibility is rep-dependent for k = 0;
the corresponding question at k ≥ 1 remains open and is the named missing
lemma `hfib_col_div_b_via_i_block`).

**Implementation note.** This is now a thin wrapper around
`fiber_int_mat_eq_via_i_block_explicit`: extract `(M_i, σ_i, h_block_i,
h_stab_i)` via `exists_stab_with_block_form_of_fiber`, then `(N_i, h_int_conj)`
via `exists_stab_int_conjugate_diagMat_cons_one`, then call the explicit
form for the substituted matrix equation.  Keeping the existing API
preserves all downstream call sites; the explicit form is used directly
by Route A's i-functional consumers. -/
private lemma fiber_int_mat_eq_via_i_block {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      (slSuccEmbed σ_i).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (N_i⁻¹ * toSL j.out).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.val := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_subst⟩ :=
    fiber_int_mat_eq_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_subst⟩

/-- **Adjugate-rearrangement of the substituted integer matrix equation,
EXPLICIT-input.**

Same algebraic content as `fiber_int_mat_eq_via_i_block_rearr` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_int_conj)`.  Returns just the
adjugate-rearranged equation
`D_a · (N_i⁻¹ · A_j) · D_b · adjugate(ν) = adjugate(slSuccEmbed σ_i) · D_c`,
where `A_j := toSL j.out` and the `ν` witness comes from the substituted
integer matrix equation produced by `fiber_int_mat_eq_via_i_block_explicit`.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit` for the architectural rationale
(preserving i-functionality of `(M_i, σ_i, N_i)` through the chain).  This
lemma is the second step in the explicit-parameter chain after the
substituted matrix equation. -/
private lemma fiber_int_mat_eq_via_i_block_rearr_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) := by
  obtain ⟨ν, h_subst⟩ :=
    fiber_int_mat_eq_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  refine ⟨ν, ?_⟩
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  set X : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (N_i⁻¹ * toSL j.out).val
    with hX_def
  have h_adj_block_block :
      Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.adjugate_mul, show (slSuccEmbed σ_i).val.det = 1 from
      (slSuccEmbed σ_i).2, one_smul]
  have h_ν_adj_ν :
      ν.val * Matrix.adjugate ν.val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.mul_adjugate, show ν.val.det = 1 from ν.2, one_smul]
  have h_premul :
      D_a * X * D_b =
        Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by
    have h : Matrix.adjugate (slSuccEmbed σ_i).val *
        ((slSuccEmbed σ_i).val * D_a * X * D_b) =
        Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by
      rw [h_subst]
    rw [show Matrix.adjugate (slSuccEmbed σ_i).val *
            ((slSuccEmbed σ_i).val * D_a * X * D_b) =
          (Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val) *
            D_a * X * D_b from by
        simp only [Matrix.mul_assoc]] at h
    rw [h_adj_block_block, Matrix.one_mul] at h
    exact h
  have h : D_a * X * D_b * Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val := by
    rw [h_premul]
  rw [show Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * D_c * (ν.val * Matrix.adjugate ν.val)
      by simp only [Matrix.mul_assoc]] at h
  rw [h_ν_adj_ν, Matrix.mul_one] at h
  exact h

/-- See `fiber_int_mat_eq_via_i_block_rearr_explicit` for the active
explicit-input rearrangement; this is now a thin wrapper that extracts
the i-side block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
private lemma fiber_int_mat_eq_via_i_block_rearr {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr⟩

/-- **j-side adjugate-rearranged equation, EXPLICIT-input.**

Same algebraic content as `fiber_int_mat_eq_via_i_block_rearr_adj` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_int_conj)`.  Derives the premultiplied
adjugate-rearranged form
`adjugate(D_b) · adjugate(X.val) · adjugate(D_a) =
  adjugate(ν.val) · adjugate(D_c) · slSuccEmbed σ_i.val`
from the rearranged equation produced by
`fiber_int_mat_eq_via_i_block_rearr_explicit`.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit`.  This is the third step in the
explicit-parameter chain after `_rearr_explicit`. -/
private lemma fiber_int_mat_eq_via_i_block_rearr_adj_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) := by
  obtain ⟨ν, h_rearr⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  refine ⟨ν, h_rearr, ?_⟩
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  have hdet_block : (slSuccEmbed σ_i).val.det = 1 := (slSuccEmbed σ_i).2
  have hdet_ν : ν.val.det = 1 := ν.2
  have h_card : Fintype.card (Fin (k + 2)) ≠ 1 := by
    simp [Fintype.card_fin]
  have h_rearr_adj := congr_arg Matrix.adjugate h_rearr
  rw [show Matrix.adjugate (D_a * (N_i⁻¹ * toSL j.out).val * D_b *
        Matrix.adjugate ν.val) =
      Matrix.adjugate (Matrix.adjugate ν.val) *
        (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a)) from by
      rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
          Matrix.adjugate_mul_distrib]] at h_rearr_adj
  rw [show Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val * D_c) =
      Matrix.adjugate D_c *
        Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val) from by
      rw [Matrix.adjugate_mul_distrib]] at h_rearr_adj
  have h_adj_adj_ν : Matrix.adjugate (Matrix.adjugate ν.val) = ν.val := by
    rw [Matrix.adjugate_adjugate _ h_card, hdet_ν, one_pow, one_smul]
  have h_adj_adj_block :
      Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val) =
        (slSuccEmbed σ_i).val := by
    rw [Matrix.adjugate_adjugate _ h_card, hdet_block, one_pow, one_smul]
  rw [h_adj_adj_ν, h_adj_adj_block] at h_rearr_adj
  have h_adj_ν_ν : Matrix.adjugate ν.val * ν.val = (1 : Matrix _ _ ℤ) := by
    rw [Matrix.adjugate_mul, hdet_ν, one_smul]
  have h_premul :
      Matrix.adjugate ν.val *
        (ν.val * (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) := by
    rw [h_rearr_adj]
  rw [show Matrix.adjugate ν.val *
        (ν.val * (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a))) =
      (Matrix.adjugate ν.val * ν.val) *
        (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a)) from by
      simp only [Matrix.mul_assoc]] at h_premul
  rw [h_adj_ν_ν, Matrix.one_mul] at h_premul
  rw [show Matrix.adjugate D_b *
        (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
          Matrix.adjugate D_a) =
      Matrix.adjugate D_b *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate D_a from by
      simp only [Matrix.mul_assoc]] at h_premul
  exact h_premul

/-- See `fiber_int_mat_eq_via_i_block_rearr_adj_explicit` for the active
explicit-input adjugate-rearrangement; this is now a thin wrapper that
extracts the i-side block witnesses via `exists_stab_with_block_form_of_fiber`
and `exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
private lemma fiber_int_mat_eq_via_i_block_rearr_adj {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr, h_adj⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_adj_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr, h_adj⟩

/-- **j-side col-divisibility on `X := N_i⁻¹ · toSL j.out`, EXPLICIT-input.**

Same algebraic content as `hfib_col_div_b_via_i_block` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, N_i, h_block_i, h_int_conj)`.
Returns the substituted matrix equation, the rearranged form, the
adjugate-rearranged form, and the col-divisibility
`∀ r : Fin (k + 1), (b r : ℤ) ∣ (X⁻¹).val r.succ 0`, all packaged in an
existential `∃ ν, ...` witness.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit`.  This is the fourth step in the
explicit-parameter chain after `_rearr_adj_explicit`. -/
private lemma hfib_col_div_b_via_i_block_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) ∧
      ∀ r : Fin (k + 1),
        (b r : ℤ) ∣ ((N_i⁻¹ * toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨ν, h_rearr, h_adj⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_adj_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  refine ⟨ν, h_rearr, h_adj, ?_⟩
  intro r
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  have hdet_block : (slSuccEmbed σ_i).val.det = 1 := (slSuccEmbed σ_i).2
  have hdet_X : (N_i⁻¹ * toSL j.out).val.det = 1 := (N_i⁻¹ * toSL j.out).2
  have hdet_ν : ν.val.det = 1 := ν.2
  have hdet_D_a : D_a.det = ∏ q : Fin (k + 1), (a q : ℤ) := by
    rw [hD_a_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hdet_D_b : D_b.det = ∏ q : Fin (k + 1), (b q : ℤ) := by
    rw [hD_b_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hdet_D_c : D_c.det = ∏ q : Fin (k + 1), (c q : ℤ) := by
    rw [hD_c_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hprod_eq :
      (∏ q : Fin (k + 1), (a q : ℤ)) * (∏ q : Fin (k + 1), (b q : ℤ)) =
      ∏ q : Fin (k + 1), (c q : ℤ) := by
    have h := congr_arg Matrix.det h_rearr
    simp only [Matrix.det_mul, Matrix.det_adjugate, hdet_block, hdet_X,
      hdet_ν, hdet_D_a, hdet_D_b, hdet_D_c, one_pow, mul_one, one_mul] at h
    exact h
  have hpc_pos : 0 < ∏ q : Fin (k + 1), (c q : ℤ) := by
    apply Finset.prod_pos
    intro q _
    exact_mod_cast hc q
  have hpc_ne : (∏ q : Fin (k + 1), (c q : ℤ)) ≠ 0 := hpc_pos.ne'
  have h_postmul :
      (∏ q : Fin (k + 1), (a q : ℤ)) •
        (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a := by
    have h : Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
          Matrix.adjugate D_a * D_a =
        Matrix.adjugate ν.val *
          (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a := by
      rw [show Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
              Matrix.adjugate D_a * D_a =
            (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
              Matrix.adjugate D_a) * D_a from rfl,
          h_adj]
    rw [show Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a * D_a =
          Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            (Matrix.adjugate D_a * D_a) by simp only [Matrix.mul_assoc]] at h
    rw [Matrix.adjugate_mul, hdet_D_a, Matrix.mul_smul, Matrix.mul_one] at h
    exact h
  have h_entry := congrFun (congrFun h_postmul r.succ) 0
  have h_LHS_simp :
      ((∏ q : Fin (k + 1), (a q : ℤ)) •
          (Matrix.adjugate D_b *
            Matrix.adjugate (N_i⁻¹ * toSL j.out).val)) r.succ 0 =
      (∏ q : Fin (k + 1), (a q : ℤ)) *
        ((∏ x ∈ Finset.univ.erase r.succ,
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) := by
    show (∏ q, (a q : ℤ)) *
        (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val) r.succ 0 =
      _
    rw [hD_b_def, Matrix.adjugate_diagonal]
    rw [show
        (Matrix.diagonal (fun i : Fin (k + 2) ↦
          ∏ x ∈ Finset.univ.erase i,
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val) r.succ 0 =
        (∏ x ∈ Finset.univ.erase r.succ,
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 from by
      rw [Matrix.diagonal_mul]]
  have h_RHS_simp :
      (Matrix.adjugate ν.val *
          (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a) r.succ 0 =
      Matrix.adjugate ν.val r.succ 0 * (∏ q : Fin (k + 1), (c q : ℤ)) := by
    have h1 :
        (Matrix.adjugate ν.val *
            (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a) r.succ 0 =
          (Matrix.adjugate ν.val *
            (Matrix.adjugate D_c * (slSuccEmbed σ_i).val)) r.succ 0 := by
      rw [hD_a_def, Matrix.mul_diagonal]
      simp [Fin.cons_zero]
    rw [h1]
    have hadjDc_block_p0 : ∀ p : Fin (k + 2),
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) p 0 =
        if p = 0 then (∏ q : Fin (k + 1), (c q : ℤ)) else 0 := by
      intro p
      rw [hD_c_def, Matrix.adjugate_diagonal, Matrix.diagonal_mul]
      refine Fin.cases ?_ ?_ p
      · rw [slSuccEmbed_val_zero_zero, mul_one, if_pos rfl]
        have hf0 : (((Fin.cons 1 c : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 := by
          simp [Fin.cons_zero]
        rw [Finset.prod_erase (Finset.univ : Finset (Fin (k + 2))) hf0]
        rw [Fin.prod_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
      · intro p'
        rw [slSuccEmbed_val_succ_zero, mul_zero, if_neg (Fin.succ_ne_zero p')]
    rw [Matrix.mul_apply]
    have hsum : ∀ (f : Fin (k + 2) → ℤ),
        (∀ p : Fin (k + 2), p ≠ 0 → f p = 0) →
        (∑ p : Fin (k + 2), f p) = f 0 := by
      intro f hf
      rw [show (∑ p, f p) = f 0 + ∑ p ∈ Finset.univ.erase 0, f p from
            (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm]
      rw [Finset.sum_eq_zero (fun p hp ↦ hf p (Finset.ne_of_mem_erase hp))]
      ring
    rw [hsum (fun p ↦ Matrix.adjugate ν.val r.succ p *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) p 0)]
    · rw [hadjDc_block_p0 0, if_pos rfl]
    · intro p hp
      rw [hadjDc_block_p0 p, if_neg hp, mul_zero]
  rw [h_LHS_simp, h_RHS_simp] at h_entry
  have h_b_in_set : r.succ ∈ (Finset.univ : Finset (Fin (k + 2))) :=
    Finset.mem_univ _
  have h_prod_b_fold :
      (∏ x ∈ Finset.univ.erase r.succ,
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
      ((b r : ℤ)) =
      ∏ q : Fin (k + 1), (b q : ℤ) := by
    have h := Finset.mul_prod_erase (Finset.univ : Finset (Fin (k + 2)))
      (fun x : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) h_b_in_set
    simp only at h
    have hfb_succ :
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) r.succ : ℕ) : ℤ) = (b r : ℤ) := by
      simp [Fin.cons_succ]
    have h_full :
        ∏ x : Fin (k + 2), (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ) =
        ∏ q : Fin (k + 1), (b q : ℤ) := by
      rw [Fin.prod_univ_succ]
      have h0 :
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 := by
        simp [Fin.cons_zero]
      rw [h0, one_mul]
      refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      simp [Fin.cons_succ]
    rw [hfb_succ, h_full] at h
    linarith [h]
  have h_mul_b_r := congr_arg (· * (b r : ℤ)) h_entry
  simp only at h_mul_b_r
  have h_LHS_b :
      (∏ q : Fin (k + 1), (a q : ℤ)) *
          ((∏ x ∈ Finset.univ.erase r.succ,
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
            Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) * (b r : ℤ) =
      (∏ q : Fin (k + 1), (c q : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 := by
    rw [show (∏ q : Fin (k + 1), (a q : ℤ)) *
            ((∏ x ∈ Finset.univ.erase r.succ,
              (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
              Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) * (b r : ℤ) =
          (∏ q : Fin (k + 1), (a q : ℤ)) *
            (((∏ x ∈ Finset.univ.erase r.succ,
              (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) * (b r : ℤ)) *
              Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) by ring]
    rw [h_prod_b_fold, ← mul_assoc, hprod_eq]
  have h_RHS_b :
      Matrix.adjugate ν.val r.succ 0 * (∏ q : Fin (k + 1), (c q : ℤ)) * (b r : ℤ) =
      (∏ q : Fin (k + 1), (c q : ℤ)) *
        ((b r : ℤ) * Matrix.adjugate ν.val r.succ 0) := by
    ring
  rw [h_LHS_b, h_RHS_b] at h_mul_b_r
  have h_X_eq :
      Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 =
        (b r : ℤ) * Matrix.adjugate ν.val r.succ 0 :=
    mul_left_cancel₀ hpc_ne h_mul_b_r
  refine ⟨Matrix.adjugate ν.val r.succ 0, ?_⟩
  have h_inv_eq : ((N_i⁻¹ * toSL j.out)⁻¹ :
      SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 =
      Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
  rw [h_inv_eq, h_X_eq]

/-- See `hfib_col_div_b_via_i_block_explicit` for the active explicit-input
col-divisibility chain; this is now a thin wrapper that extracts the i-side
block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
private lemma hfib_col_div_b_via_i_block {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) ∧
      ∀ r : Fin (k + 1),
        (b r : ℤ) ∣ ((N_i⁻¹ * toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr, h_adj, h_div⟩ :=
    hfib_col_div_b_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr, h_adj, h_div⟩

/-- **X-side block-form witness from the substituted fiber.**
Mirror of `exists_stab_with_block_form_of_fiber` but for the SUBSTITUTED
matrix `X := N_i⁻¹ * toSL j.out`, where `N_i` is the integer-conjugate
companion of the i-side stabilizer factor `M_i` (both extracted from
`hfib_col_div_b_via_i_block`).

Produces `M_X ∈ SL(k+2, ℤ)` in the `Fin.cons 1 b`-diagonal-conjugation
stabilizer plus `τ_X ∈ SL(k+1, ℤ)` such that
  `(N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X`.

This is the j-side analog of the i-side block form. The proof mirrors
the i-side template:
1. Apply `hfib_col_div_b_via_i_block` to obtain `N_i` and the chain
   divisibility `b r ∣ X⁻¹.{r.succ, 0}`.
2. Apply `sl_first_col_primitive (X⁻¹)` for primitivity of X⁻¹'s first
   column.
3. Feed both into `sl_exists_col_stab_divChain b hb hdb` to obtain
   `M_0_X ∈ stab(D_b)` with first column matching X⁻¹'s first column.
4. Compute `(X * M_0_X).first_col = (X * X⁻¹).first_col = e_0`.
5. Apply `sl_first_row_clear_with_col0_e0 b hb` to clear the first row.
6. Combine into `M_X := M_0_X * T_clear` (in stab(D_b) by mul-closure).
7. The product `(X * M_X)` has first row and first column = e_0, hence
   equals `slSuccEmbed τ_X` for `τ_X` the bottom-right block.

The exposed `M_i`, `N_i`, plus the integer conjugation identity
`D_a · N_i = M_i · D_a`, support the eventual N_i-bridge to a canonical
j-side block form on `toSL j.out` (the next-stint deliverable). -/
private lemma exists_stab_with_block_form_of_X_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_i N_i M_X : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      (N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_subst, h_rearr_adj, h_div⟩ :=
    hfib_col_div_b_via_i_block a b c ha hb hc hda i j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out with hX_def
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2), d ∣ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0) →
        IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (X⁻¹) d hd
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_div
  have h_col_e0 : ∀ r : Fin (k + 2),
      (X * M_0_X).val r 0 =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    have h_to_inv :
        (X * M_0_X).val r 0 = (X * X⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      rw [hM_0_X_col p]
    rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (X * M_0_X) h_col_e0 Finset.univ
  set M_X : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0_X * T_clear with hM_X_def
  set N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (X * M_X).val with hN_def
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := by
    rw [hM_X_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (X * M_X).val r 0 = _
    rw [hM_X_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0 := by
    intro l
    show (X * M_X).val 0 l.succ = _
    rw [hM_X_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set τ_X_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N I.succ J.succ with hτ_raw_def
  have h_det : τ_X_raw.det = 1 := by
    have h_det_N : N.det = 1 := by
      rw [hN_def]; exact (X * M_X).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N 0 j.succ *
            (N.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_X_raw := by
      ext I J
      show N I.succ ((0 : Fin (k + 2)).succAbove J) = τ_X_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_X_raw, h_det⟩ with hτ_X_def
  refine ⟨M_i, N_i, M_X, τ_X, h_stab_i, h_int_conj, ?_, ?_⟩
  · -- (X * M_X) = slSuccEmbed τ_X.
    apply Subtype.ext
    ext I J
    show N I J = (slSuccEmbed τ_X).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  · -- M_X ∈ stab(D_b).
    have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_0_X : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) *
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) := by
      rw [hM_X_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_X_stab hT_stab

/-- **j-side X-class-preimage bridge (corrected representative).**
From `exists_stab_with_block_form_of_X_fiber` (which produces `M_X ∈ stab(D_b)`
and `τ_X ∈ SL_(k+1)(ℤ)` with `(N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X`),
construct the dim-(k+1) quotient class `j_m := ⟦τ_X_H⟧` and prove the
**corrected** class equality at dim (k+2):

  `decompQuot_slSuccEmbed_diagMat b hb j_m = ⟦j_corrected⟧`

where `j_corrected : (GL_pair (k+2)).H := ⟨mapGL ℚ N_i⁻¹, _⟩ * j.out`.

This is the j-side analog of `exists_i_m_block_class_eq_of_fiber`, but with
the `N_i`-corrected representative instead of `j.out` directly. The class
`⟦j_corrected⟧` differs from `j` by the i-side conjugation factor
`mapGL ℚ N_i⁻¹`; in general these are NOT the same class in
`decompQuot ... (Fin.cons 1 b)`, since `mapGL ℚ N_i⁻¹` need not be in the
`Fin.cons 1 b` stabilizer.

Closing the residual `fiber_has_block_form_preimages` from this corrected
class bridge requires either:
* a sibling of `fiber_has_block_form_preimages_existential_reps` that
  accepts the corrected representative `j_corrected` (delegating the
  N_i-correction to the consumer); or
* a separate proof that `⟦j_corrected⟧ = j` in
  `decompQuot ... (Fin.cons 1 b)`, which would require
  `mapGL ℚ N_i⁻¹ ∈ stab(D_b)` — generally FALSE since N_i comes from
  the `D_a`-stab, not `D_b`-stab.

This lemma is therefore the strongest build-clean X-side bridge available
without modifying the consumer or assuming additional structure on N_i. -/
private lemma exists_j_m_X_block_class_eq_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) := by
  obtain ⟨M_i, N_i, M_X, τ_X, h_stab_i, h_int_conj, h_X_block, h_M_X_stab⟩ :=
    exists_stab_with_block_form_of_X_fiber a b c ha hb hc hda hdb i j hfib
  set τ_X_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩
    with hτ_X_H_def
  set N_i_inv_H : (GL_pair (k + 2)).H :=
    ⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ with hN_i_inv_H_def
  set j_corrected : (GL_pair (k + 2)).H := N_i_inv_H * j.out with hj_corr_def
  refine ⟨M_i, N_i, ⟦τ_X_H⟧, h_stab_i, h_int_conj, ?_⟩
  change (⟦slSuccEmbed_H τ_X_H⟧ :
    decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
    (⟦j_corrected⟧ : decompQuot _ _)
  apply Quotient.sound
  change QuotientGroup.leftRel _ (slSuccEmbed_H τ_X_H) j_corrected
  rw [QuotientGroup.leftRel_apply]
  rw [mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
  have h_toSL : toSL τ_X_H = τ_X := by
    apply mapGL_injective (k + 1)
    rw [toSL_spec]
  have h_GL_val :
      (((slSuccEmbed_H τ_X_H)⁻¹ * j_corrected : (GL_pair (k + 2)).H) :
        GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M_X)⁻¹ := by
    have h_slSuccEmbed_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
      show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
      rw [h_toSL, ← h_X_block, map_mul, map_mul, toSL_spec]
    push_cast
    rw [h_slSuccEmbed_GL]
    show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
      (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
    group
  rw [h_GL_val]
  have h_inv_form : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 b) =
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ * (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b))⁻¹ := by
    group
  rw [h_inv_form]
  exact inv_mem h_M_X_stab

/-- **Corrected-j fiber descent, EXPLICIT-input.**

Same algebraic content as `fiber_block_form_preimage_corrected_j` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)`.  Returns the corrected
j-class equality referencing the **caller's** `N_i` (rather than
extracting one from a j-dependent existential).

**Use site.**  Combined with i-only `Classical.choose` extraction of
`(M_i, σ_i, N_i)` via `exists_stab_with_block_form_of_fiber` (i-only body)
and `exists_stab_int_conjugate_diagMat_cons_one` (i-only body given
`M_i`), the caller obtains an i-functional `N_i` and the corresponding
i-functional corrected-j descent output.  This is the fifth and main
step in the explicit-parameter Route A chain.

The body is a parameterized version of `fiber_block_form_preimage_corrected_j`'s
proof: it skips the `hfib_col_div_b_via_i_block` extraction (replaced by the
explicit inputs), then uses `hfib_col_div_b_via_i_block_explicit` to get
`h_div`, after which the X-side block construction proceeds identically. -/
private lemma fiber_block_form_preimage_corrected_j_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i_H τ_X_H : (GL_pair (k + 1)).H),
      decompQuot_slSuccEmbed_diagMat a ha
        (⟦σ_i_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i ∧
      decompQuot_slSuccEmbed_diagMat b hb
        (⟦τ_X_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      (diagMat (k + 1) c)⁻¹ * (σ_i_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a *
        (τ_X_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  obtain ⟨_ν, _, _, h_div⟩ :=
    hfib_col_div_b_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out with hX_def
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2), d ∣ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0) →
        IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (X⁻¹) d hd
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_div
  have h_col_e0 : ∀ r : Fin (k + 2),
      (X * M_0_X).val r 0 =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    have h_to_inv :
        (X * M_0_X).val r 0 = (X * X⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      rw [hM_0_X_col p]
    rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (X * M_0_X) h_col_e0 Finset.univ
  set M_X : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0_X * T_clear with hM_X_def
  set N_full : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (X * M_X).val with hN_def
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := by
    rw [hM_X_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N_full r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (X * M_X).val r 0 = _
    rw [hM_X_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N_full 0 l.succ = 0 := by
    intro l
    show (X * M_X).val 0 l.succ = _
    rw [hM_X_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N_full 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N_full I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set τ_X_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N_full I.succ J.succ with hτ_raw_def
  have h_det : τ_X_raw.det = 1 := by
    have h_det_N : N_full.det = 1 := by
      rw [hN_def]; exact (X * M_X).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N_full 0 j.succ *
            (N_full.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N_full.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_X_raw := by
      ext I J
      show N_full I.succ ((0 : Fin (k + 2)).succAbove J) = τ_X_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_X_raw, h_det⟩ with hτ_X_def
  have h_X_block : X * M_X = slSuccEmbed τ_X := by
    apply Subtype.ext
    ext I J
    show N_full I J = (slSuccEmbed τ_X).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  have h_M_X_stab : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
    have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_0_X : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) *
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) := by
      rw [hM_X_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_X_stab hT_stab
  refine ⟨⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩,
    ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩, ?_, ?_, ?_⟩
  · -- i-side class equality.
    rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    change ⟦slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩⟧ =
      (⟦i.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _
      (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩) i.out
    rw [QuotientGroup.leftRel_apply]
    rw [mem_diagMat_cons_stabilizer_subgroupOf_iff a ha]
    set σ_i_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ with hσ_i_H_def
    have h_toSL : toSL σ_i_H = σ_i := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H σ_i_H)⁻¹ * i.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_i)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_i_H)) = _
        rw [h_toSL, ← h_block_i, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_i
  · -- corrected j-side class equality.
    set τ_X_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ with hτ_X_H_def
    set j_corr : (GL_pair (k + 2)).H :=
      (⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) * j.out
      with hj_corr_def
    change (⟦slSuccEmbed_H τ_X_H⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
      (⟦j_corr⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H τ_X_H) j_corr
    rw [QuotientGroup.leftRel_apply]
    rw [mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
    have h_toSL : toSL τ_X_H = τ_X := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H τ_X_H)⁻¹ * j_corr : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_X)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
        show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
        rw [h_toSL, ← h_X_block, map_mul, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]
      show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
        (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
      group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_M_X_stab
  · -- dim-(k+1) fiber mem_H for (σ_i_H, τ_X_H).
    set σ_i_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ with hσ_i_H_def
    set τ_X_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ with hτ_X_H_def
    have h_lifted_mem_H :
        (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
          (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) *
          (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
      have h_toSL_σ : toSL σ_i_H = σ_i := by
        apply mapGL_injective (k + 1); rw [toSL_spec]
      have h_toSL_τ : toSL τ_X_H = τ_X := by
        apply mapGL_injective (k + 1); rw [toSL_spec]
      have h_slSucc_σ_GL : (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_i_H)) = _
        rw [h_toSL_σ, ← h_block_i, map_mul, toSL_spec]
      have h_slSucc_τ_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
        show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
        rw [h_toSL_τ, ← h_X_block, map_mul, map_mul, toSL_spec]
      have h_int_conj_GL :
          diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) := by
        have hcons_pos : ∀ q, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) q :=
          cons_one_pos ha
        have h := congr_arg
          (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦
            M.map (algebraMap ℤ ℚ)) h_int_conj
        simp only [Matrix.map_mul] at h
        apply Units.ext
        simp only [Units.val_mul, mapGL_coe_matrix,
          diagMat_val (k + 2) _ hcons_pos]
        rw [show (Matrix.diagonal (fun r : Fin (k + 2) ↦
              (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
            Matrix.diagonal
              (fun r : Fin (k + 2) ↦
                (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℚ)) from by
          rw [Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
          congr 1] at h
        convert h using 1
      have h_invN : (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) = (mapGL ℚ N_i)⁻¹ := by
        rw [← map_inv]
      have h_cancel :
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) =
          diagMat (k + 2) (Fin.cons 1 a) := by
        rw [h_invN, ← h_int_conj_GL]
        group
      have h_main :
          (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
            (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 b) =
          ((diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
            (i.out : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (j.out : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 b)) *
          ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ * (mapGL ℚ M_X) *
            diagMat (k + 2) (Fin.cons 1 b)) := by
        rw [h_slSucc_σ_GL, h_slSucc_τ_GL]
        have h_rebracket :
            (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
              ((i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i) *
              diagMat (k + 2) (Fin.cons 1 a) *
              ((mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X) *
              diagMat (k + 2) (Fin.cons 1 b) =
            (diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (i.out : GL (Fin (k + 2)) ℚ) *
              ((mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
                diagMat (k + 2) (Fin.cons 1 a) *
                (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ)) *
              (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X *
              diagMat (k + 2) (Fin.cons 1 b) := by
          group
        rw [h_rebracket, h_cancel]
        group
      rw [h_main]
      apply mul_mem
      · exact hfib_to_mem_H a b c ha hb hc i j hfib
      · exact h_M_X_stab
    exact slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc σ_i_H τ_X_H
      h_lifted_mem_H

/-- **Corrected-representative fiber descent (j-side via X).**
Combine the i-side block witness from `exists_stab_with_block_form_of_fiber`
with the X-side block witness from `exists_stab_with_block_form_of_X_fiber`
plus the integer conjugation identity `M_i · D_a = D_a · N_i` to produce the
dim-(k+1) data `(i_m, j_m, σ_i_H, τ_X_H)` plus:
1. canonical i-side class equality `decompQuot_slSuccEmbed_diagMat a ha i_m = i`;
2. corrected j-side class equality
   `decompQuot_slSuccEmbed_diagMat b hb j_m = ⟦j_corrected⟧` where
   `j_corrected := ⟨mapGL ℚ N_i⁻¹, _⟩ * j.out`;
3. dim-(k+1) fiber set-form for the explicit reps `(σ_i_H, τ_X_H)` of
   `(i_m, j_m)`:
     `{σ_i_H · D_a} * {τ_X_H · D_b} * H_{k+1} = {D_c} * H_{k+1}`.

**Algebraic core.** The dim-(k+2) lifted mem_H expression
`(D_c')⁻¹ · slSuccEmbed_H σ_i_H · D_a' · slSuccEmbed_H τ_X_H · D_b'` simplifies
via the GL-level forms of the i-side and X-side block witnesses to
`((D_c')⁻¹ · i.out · D_a' · j.out · D_b') · (mapGL ℚ M_X-conjugate)`. The
first factor is in `H_{k+2}` by the original fiber condition; the second is in
`H_{k+2}` by `M_X ∈ stab(D_b)`'s GL-image lying in the H subgroup-of-stab.
The product is in `H_{k+2}`, which by `slSuccEmbed_H_fiber_transfer_converse`
descends to the dim-(k+1) mem_H form, and by `fiber_diagMat_iff_mem_H`
to the set-form on `(σ_i_H, τ_X_H)`. The j-side correction `mapGL ℚ N_i⁻¹`
appears in the class equality output (via
`exists_j_m_X_block_class_eq_of_fiber`), but it CANCELS in the dim-(k+2)
mem_H computation through the integer conjugation identity (since
`mapGL M_i · D_a' · mapGL N_i⁻¹ = D_a'`).

**Note on canonical-rep set-form.** The set-form output uses `σ_i_H, τ_X_H`
(specific representatives of `i_m, j_m`), NOT the canonical
`i_m.out, j_m.out`. The joint set-form is rep-DEPENDENT in general, so this
is the strongest statement provable without additional rep-control input
(see the documented dim-2 counterexample at the docstring of
`fiber_has_block_form_preimages`). -/
private lemma fiber_block_form_preimage_corrected_j {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (σ_i_H τ_X_H : (GL_pair (k + 1)).H),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      decompQuot_slSuccEmbed_diagMat a ha
        (⟦σ_i_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i ∧
      decompQuot_slSuccEmbed_diagMat b hb
        (⟦τ_X_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      (diagMat (k + 1) c)⁻¹ * (σ_i_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a *
        (τ_X_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  obtain ⟨σ_i, M_i, N_i, _, h_block_i, h_stab_i, h_int_conj, _, _, h_div⟩ :=
    hfib_col_div_b_via_i_block a b c ha hb hc hda i j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out with hX_def
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2), d ∣ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0) →
        IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (X⁻¹) d hd
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_div
  have h_col_e0 : ∀ r : Fin (k + 2),
      (X * M_0_X).val r 0 =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    have h_to_inv :
        (X * M_0_X).val r 0 = (X * X⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      rw [hM_0_X_col p]
    rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (X * M_0_X) h_col_e0 Finset.univ
  set M_X : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0_X * T_clear with hM_X_def
  set N_full : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (X * M_X).val with hN_def
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := by
    rw [hM_X_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N_full r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (X * M_X).val r 0 = _
    rw [hM_X_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N_full 0 l.succ = 0 := by
    intro l
    show (X * M_X).val 0 l.succ = _
    rw [hM_X_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N_full 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N_full I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set τ_X_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N_full I.succ J.succ with hτ_raw_def
  have h_det : τ_X_raw.det = 1 := by
    have h_det_N : N_full.det = 1 := by
      rw [hN_def]; exact (X * M_X).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N_full 0 j.succ *
            (N_full.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N_full.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_X_raw := by
      ext I J
      show N_full I.succ ((0 : Fin (k + 2)).succAbove J) = τ_X_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_X_raw, h_det⟩ with hτ_X_def
  have h_X_block : X * M_X = slSuccEmbed τ_X := by
    apply Subtype.ext
    ext I J
    show N_full I J = (slSuccEmbed τ_X).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  have h_M_X_stab : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
    have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_0_X : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) *
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) := by
      rw [hM_X_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_X_stab hT_stab
  refine ⟨M_i, N_i, ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩,
    ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩,
    h_stab_i, h_int_conj, ?_, ?_, ?_⟩
  · rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    change ⟦slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩⟧ =
      (⟦i.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _
      (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩) i.out
    rw [QuotientGroup.leftRel_apply]
    rw [mem_diagMat_cons_stabilizer_subgroupOf_iff a ha]
    set σ_i_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ with hσ_i_H_def
    have h_toSL : toSL σ_i_H = σ_i := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H σ_i_H)⁻¹ * i.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_i)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_i_H)) = _
        rw [h_toSL, ← h_block_i, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_i
  · set τ_X_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ with hτ_X_H_def
    set j_corr : (GL_pair (k + 2)).H :=
      (⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) * j.out
      with hj_corr_def
    change (⟦slSuccEmbed_H τ_X_H⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
      (⟦j_corr⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H τ_X_H) j_corr
    rw [QuotientGroup.leftRel_apply]
    rw [mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
    have h_toSL : toSL τ_X_H = τ_X := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H τ_X_H)⁻¹ * j_corr : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_X)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
        show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
        rw [h_toSL, ← h_X_block, map_mul, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]
      show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
        (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
      group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_M_X_stab
  · set σ_i_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ with hσ_i_H_def
    set τ_X_H : (GL_pair (k + 1)).H :=
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ with hτ_X_H_def
    have h_lifted_mem_H :
        (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
          (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) *
          (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
      have h_toSL_σ : toSL σ_i_H = σ_i := by
        apply mapGL_injective (k + 1); rw [toSL_spec]
      have h_toSL_τ : toSL τ_X_H = τ_X := by
        apply mapGL_injective (k + 1); rw [toSL_spec]
      have h_slSucc_σ_GL : (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_i_H)) = _
        rw [h_toSL_σ, ← h_block_i, map_mul, toSL_spec]
      have h_slSucc_τ_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
        show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
        rw [h_toSL_τ, ← h_X_block, map_mul, map_mul, toSL_spec]
      have h_int_conj_GL :
          diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) := by
        have hcons_pos : ∀ q, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) q :=
          cons_one_pos ha
        have h := congr_arg
          (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦
            M.map (algebraMap ℤ ℚ)) h_int_conj
        simp only [Matrix.map_mul] at h
        apply Units.ext
        simp only [Units.val_mul, mapGL_coe_matrix,
          diagMat_val (k + 2) _ hcons_pos]
        rw [show (Matrix.diagonal (fun r : Fin (k + 2) ↦
              (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
            Matrix.diagonal
              (fun r : Fin (k + 2) ↦
                (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℚ)) from by
          rw [Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
          congr 1] at h
        convert h using 1
      have h_invN : (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) = (mapGL ℚ N_i)⁻¹ := by
        rw [← map_inv]
      have h_cancel :
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) =
          diagMat (k + 2) (Fin.cons 1 a) := by
        rw [h_invN, ← h_int_conj_GL]
        group
      have h_main :
          (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
            (slSuccEmbed_H σ_i_H : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 b) =
          ((diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
            (i.out : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) *
            (j.out : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 b)) *
          ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ * (mapGL ℚ M_X) *
            diagMat (k + 2) (Fin.cons 1 b)) := by
        rw [h_slSucc_σ_GL, h_slSucc_τ_GL]
        have h_rebracket :
            (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
              ((i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i) *
              diagMat (k + 2) (Fin.cons 1 a) *
              ((mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X) *
              diagMat (k + 2) (Fin.cons 1 b) =
            (diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (i.out : GL (Fin (k + 2)) ℚ) *
              ((mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
                diagMat (k + 2) (Fin.cons 1 a) *
                (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ)) *
              (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X *
              diagMat (k + 2) (Fin.cons 1 b) := by
          group
        rw [h_rebracket, h_cancel]
        group
      rw [h_main]
      apply mul_mem
      · -- (D_c')⁻¹ * i.out * D_a' * j.out * D_b' ∈ H from the original fiber.
        exact hfib_to_mem_H a b c ha hb hc i j hfib
      · -- M_X ∈ stab(D_b) at GL level.
        exact h_M_X_stab
    exact slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc σ_i_H τ_X_H
      h_lifted_mem_H

/-- **`mulMap` rep-invariance from a specific-rep set-form.**  If specific
representatives `σ τ : (GL_pair n).H` satisfy the left-coset (set-form) fiber
identity for `(g₁, g₂, d)`, then the rep-invariant `mulMap` value at the
corresponding classes `(⟦σ⟧, ⟦τ⟧)` equals `⟦d⟧` in `HeckeCoset`.

This is the bridge from rep-DEPENDENT set-form predicates (which the corrected
descent helper produces in the form mem_H ↔ set-form for `σ_i_H, τ_X_H`) to the
rep-INVARIANT `mulMap` value (which `heckeMultiplicityMulMap` consumes).

The proof technique mirrors the inline computation inside
`HeckeRing.mem_mulSupport_of_product_mem`: extract the stabilizer-coset shifts
relating `σ` to `(⟦σ⟧).out` (via `QuotientGroup.mk_out_eq_mul`), absorb the
shift into the H-flanks of the double coset, and conclude via
`HeckeCoset.doubleCoset_eq_of_mem`. -/
private lemma mulMap_eq_of_setForm_specific_reps {n : ℕ} [NeZero n]
    (g₁ g₂ d : (GL_pair n).Δ) (σ τ : (GL_pair n).H)
    (h_set : ({(σ : GL (Fin n) ℚ) * (g₁ : GL (Fin n) ℚ)} : Set _) *
        {(τ : GL (Fin n) ℚ) * (g₂ : GL (Fin n) ℚ)} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(d : GL (Fin n) ℚ)} *
          ((GL_pair n).H : Set (GL (Fin n) ℚ))) :
    HeckeRing.mulMap (GL_pair n) g₁ g₂ ⟨⟦σ⟧, ⟦τ⟧⟩ =
      (⟦d⟧ : HeckeRing.HeckeCoset (GL_pair n)) := by
  have h_prod_mem : (σ : GL (Fin n) ℚ) * g₁ *
      ((τ : GL (Fin n) ℚ) * g₂) ∈
      DoubleCoset.doubleCoset ((d : GL (Fin n) ℚ))
        (GL_pair n).H (GL_pair n).H := by
    rw [Set.singleton_mul_singleton] at h_set
    have h_in : (σ : GL (Fin n) ℚ) * g₁ * ((τ : GL (Fin n) ℚ) * g₂) ∈
        ({(d : GL (Fin n) ℚ)} : Set _) *
          ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
      rw [← h_set]
      exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
    obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in
    rw [Set.mem_singleton_iff] at hd_eq
    subst hd_eq
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨1, (GL_pair n).H.one_mem, h, hh, ?_⟩
    simp only [one_mul]
    exact hprod.symm
  unfold HeckeRing.mulMap
  rw [HeckeRing.HeckeCoset.eq_iff]
  dsimp only
  apply HeckeRing.HeckeCoset.doubleCoset_eq_of_mem
  obtain ⟨n_a, hn_a⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₁ : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf
      (GL_pair n).H) σ
  obtain ⟨n_b, hn_b⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₂ : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf
      (GL_pair n).H) τ
  have hi_out :
      ((⟦σ⟧ : decompQuot (GL_pair n) g₁).out : GL (Fin n) ℚ) =
        (σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) := by
    have := congr_arg (Subtype.val : (GL_pair n).H → GL (Fin n) ℚ) hn_a
    simpa [Subgroup.coe_mul]
  have hj_out :
      ((⟦τ⟧ : decompQuot (GL_pair n) g₂).out : GL (Fin n) ℚ) =
        (τ : GL (Fin n) ℚ) * (n_b : GL (Fin n) ℚ) := by
    have := congr_arg (Subtype.val : (GL_pair n).H → GL (Fin n) ℚ) hn_b
    simpa [Subgroup.coe_mul]
  have hn_a_conj :
      (g₁ : GL (Fin n) ℚ)⁻¹ * (n_a : GL (Fin n) ℚ) * g₁ ∈ (GL_pair n).H := by
    have := n_a.2
    rw [Subgroup.mem_subgroupOf,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct]
  have hn_b_conj :
      (g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂ ∈ (GL_pair n).H := by
    have := n_b.2
    rw [Subgroup.mem_subgroupOf,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct]
  rw [hi_out, hj_out]
  rw [DoubleCoset.mem_doubleCoset] at h_prod_mem
  obtain ⟨a', ha', b', hb', habp⟩ := h_prod_mem
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨(σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
      (σ : GL (Fin n) ℚ)⁻¹ * a',
    (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem
        ((GL_pair n).H.mul_mem σ.2 (SetLike.coe_mem n_a.val))
        ((GL_pair n).H.inv_mem σ.2))
      ha',
    b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂),
    (GL_pair n).H.mul_mem hb' hn_b_conj, ?_⟩
  have h_eq : ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
        (σ : GL (Fin n) ℚ)⁻¹ * a') * (d : GL (Fin n) ℚ) *
        (b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂)) =
      (σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) * g₁ *
        ((τ : GL (Fin n) ℚ) * (n_b : GL (Fin n) ℚ) * g₂) := by
    have h1 : ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
          (σ : GL (Fin n) ℚ)⁻¹ * a') * (d : GL (Fin n) ℚ) *
          (b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂)) =
        ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
          (σ : GL (Fin n) ℚ)⁻¹) *
          ((a' : GL (Fin n) ℚ) * d * b') *
          ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂) := by group
    rw [h1, ← habp]
    group
  exact h_eq.symm

/-- **Corrected-j mulMap-form descent, EXPLICIT-input.**

Same as `fiber_block_form_preimage_corrected_j_mulMap` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)`.
Returns the dim-(k+1) class pair `(i_m, j_m)` plus canonical i-side class
equality, **corrected** j-side class equality (with caller's `N_i⁻¹`-twist),
and the rep-invariant `mulMap` evaluation `mulMap ⟨i_m, j_m⟩ = ⟦D_c_(k+1)⟧`.

This is the final step in the explicit-parameter Route A chain.  Combined
with i-only `Classical.choose` extraction of `(M_i, σ_i, N_i)` at the call
site, the output's corrected j-class equality references the i-functional
`N_i`, exactly the form consumed by
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`'s
`h_iFunctional` hypothesis. -/
private lemma fiber_block_form_preimage_corrected_j_mulMap_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  obtain ⟨σ_i_H, τ_X_H, h_class_i, h_class_j, h_fiber⟩ :=
    fiber_block_form_preimage_corrected_j_explicit a b c ha hb hc hdb i M_i σ_i
      h_block_i h_stab_i N_i h_int_conj j hfib
  refine ⟨⟦σ_i_H⟧, ⟦τ_X_H⟧, h_class_i, h_class_j, ?_⟩
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  have h_set := (fiber_diagMat_iff_mem_H a b c ha hb hc σ_i_H τ_X_H).mpr h_fiber
  have h_dval_a : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  exact mulMap_eq_of_setForm_specific_reps
    (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
    (diagMat_delta (k + 1) c) σ_i_H τ_X_H
    (by simp only [h_dval_a, h_dval_b, h_dval_c]; exact h_set)

/-- See `fiber_block_form_preimage_corrected_j_mulMap_explicit` for the active
explicit-input mulMap descent; this is now a thin wrapper that extracts the
i-side block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
private lemma fiber_block_form_preimage_corrected_j_mulMap {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨i_m, j_m, h_class_i, h_class_j, h_mulMap⟩ :=
    fiber_block_form_preimage_corrected_j_mulMap_explicit a b c ha hb hc hdb i
      M_i σ_i h_block_i h_stab_i N_i h_int_conj j hfib
  exact ⟨N_i, i_m, j_m, h_class_i, h_class_j, h_mulMap⟩

/-- **GL-level reduction for the witness-specific j.out-conjugated b-stabilizer
(T192 helper).**

Given the GL-level fiber equation `i.out · D_a · j.out · D_b = D_c · mapGL ν`,
the GL-level integer-conjugate identity `D_a · mapGL N_i = mapGL M_i · D_a`,
and the c-stabilizer condition
`D_c⁻¹ · (i.out · mapGL M_i · i.out⁻¹) · D_c ∈ H`,
deduce the j.out-conjugated b-stabilizer condition that
`fiber_block_form_preimage_canonical_j_witness_specific` consumes:
```
D_b⁻¹ · (j.out⁻¹ · mapGL N_i · j.out) · D_b ∈ H.
```

**Proof idea.** From `h_fib_GL` derive
`D_b⁻¹ · j.out⁻¹ = (mapGL ν)⁻¹ · D_c⁻¹ · i.out · D_a` and the matching
`j.out · D_b = D_a⁻¹ · i.out⁻¹ · D_c · mapGL ν`. Substituting into the goal
collapses (via `D_a · mapGL N_i · D_a⁻¹ = mapGL M_i` from `h_int_conj_GL`) to
`(mapGL ν)⁻¹ · (D_c⁻¹ · (i.out · mapGL M_i · i.out⁻¹) · D_c) · mapGL ν`,
which lies in `H` by `h_iMi_c_stab` plus subgroup closure
(since `mapGL ν ∈ H`).

This isolates the remaining substantive arithmetic into the c-stabilizer
hypothesis `h_iMi_c_stab`; the GL-level chain of substitutions is mechanical.
The reduction does **not** prove `h_iMi_c_stab` itself — that is the precise
remaining out-of-T001-scope arithmetic input
(`A_i · mapGL M_i · A_i⁻¹ ∈ stab(D_c)`, requiring SNF/multi-modular Bezout
infrastructure flagged in the architectural-blocker docblock below). -/
private lemma jout_conj_N_i_stab_of_iMi_c_stab {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_fib_GL :
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
        (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) =
      diagMat (k + 2) (Fin.cons 1 c) * (mapGL ℚ ν : GL (Fin (k + 2)) ℚ))
    (h_int_conj_GL :
      diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a))
    (h_iMi_c_stab :
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        ((i.out : GL (Fin (k + 2)) ℚ) * (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          (i.out : GL (Fin (k + 2)) ℚ)⁻¹) *
        diagMat (k + 2) (Fin.cons 1 c) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  let _ := ha; let _ := hb; let _ := hc
  set i_g : GL (Fin (k + 2)) ℚ := (i.out : GL (Fin (k + 2)) ℚ)
  set j_g : GL (Fin (k + 2)) ℚ := (j.out : GL (Fin (k + 2)) ℚ)
  set D_a : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 a)
  set D_b : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 b)
  set D_c : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 c)
  set N_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ)
  set M_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)
  set ν_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ ν : GL (Fin (k + 2)) ℚ)
  have h_fwd : j_g * D_b = D_a⁻¹ * i_g⁻¹ * D_c * ν_g := by
    have hcong :
        (D_a⁻¹ * i_g⁻¹) * (i_g * D_a * j_g * D_b) =
          (D_a⁻¹ * i_g⁻¹) * (D_c * ν_g) := by
      rw [h_fib_GL]
    calc j_g * D_b
        = (D_a⁻¹ * i_g⁻¹) * (i_g * D_a * j_g * D_b) := by group
      _ = (D_a⁻¹ * i_g⁻¹) * (D_c * ν_g) := hcong
      _ = D_a⁻¹ * i_g⁻¹ * D_c * ν_g := by group
  have h_inv : D_b⁻¹ * j_g⁻¹ = ν_g⁻¹ * D_c⁻¹ * i_g * D_a := by
    have hinv_eq : (j_g * D_b)⁻¹ = (D_a⁻¹ * i_g⁻¹ * D_c * ν_g)⁻¹ :=
      congr_arg (·⁻¹) h_fwd
    rw [show (j_g * D_b)⁻¹ = D_b⁻¹ * j_g⁻¹ by group,
        show (D_a⁻¹ * i_g⁻¹ * D_c * ν_g)⁻¹ = ν_g⁻¹ * D_c⁻¹ * i_g * D_a from
          by group] at hinv_eq
    exact hinv_eq
  have h_int : D_a * N_g * D_a⁻¹ = M_g := by
    calc D_a * N_g * D_a⁻¹
        = (M_g * D_a) * D_a⁻¹ := by rw [h_int_conj_GL]
      _ = M_g := by group
  have h_goal_eq :
      D_b⁻¹ * (j_g⁻¹ * N_g * j_g) * D_b =
        ν_g⁻¹ * (D_c⁻¹ * (i_g * M_g * i_g⁻¹) * D_c) * ν_g := by
    calc D_b⁻¹ * (j_g⁻¹ * N_g * j_g) * D_b
        = (D_b⁻¹ * j_g⁻¹) * N_g * (j_g * D_b) := by group
      _ = (ν_g⁻¹ * D_c⁻¹ * i_g * D_a) * N_g *
            (D_a⁻¹ * i_g⁻¹ * D_c * ν_g) := by rw [h_inv, h_fwd]
      _ = ν_g⁻¹ * D_c⁻¹ * i_g * (D_a * N_g * D_a⁻¹) * i_g⁻¹ * D_c * ν_g := by
            group
      _ = ν_g⁻¹ * D_c⁻¹ * i_g * M_g * i_g⁻¹ * D_c * ν_g := by rw [h_int]
      _ = ν_g⁻¹ * (D_c⁻¹ * (i_g * M_g * i_g⁻¹) * D_c) * ν_g := by group
  rw [h_goal_eq]
  have h_ν_in_H : ν_g ∈ (GL_pair (k + 2)).H := coe_mem_SLnZ (k + 2) ν
  have h_ν_inv_in_H : ν_g⁻¹ ∈ (GL_pair (k + 2)).H :=
    (GL_pair (k + 2)).H.inv_mem h_ν_in_H
  exact (GL_pair (k + 2)).H.mul_mem
    ((GL_pair (k + 2)).H.mul_mem h_ν_inv_in_H h_iMi_c_stab) h_ν_in_H

/-- **T193 chain consumer: witness-specific b-stabilizer from the c-stab
hypothesis.**

Combines the three T192/T193 bridges (`hfib_GL_eq`, `h_int_conj_GL_of_int_mat`,
`jout_conj_N_i_stab_of_iMi_c_stab`) and `exists_stab_with_block_form_of_X_fiber`
into a single conditional consumer: given the universal c-stab hypothesis on
the i.out-conjugate of any `M_i ∈ SL(ℤ)`, produce an `N_i` and the
witness-specific j.out-conjugated b-stabilizer condition consumed by
`fiber_block_form_preimage_canonical_j_witness_specific`.

This isolates the sole remaining substantive obligation
(`h_iMi_c_stab : ∀ M_i, ...`) and demonstrates the three bridges chain
mechanically through the corrected-j route. The `h_iMi_c_stab` quantifier
captures the exact "for the specific M_i extracted by
`exists_stab_with_block_form_of_X_fiber`" semantics — instantiation at the
extracted M_i is the only consumer-side step.

The `h_iMi_c_stab` obligation itself remains the SNF/multi-modular Bezout
arithmetic flagged in the architectural-blocker docblock at lines 8617-8623,
out of T001 prototype scope. -/
private lemma jout_conj_N_i_stab_for_X_fiber_of_iMi_c_stab {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _))
    (h_iMi_c_stab :
      ∀ M_i : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
          ((i.out : GL (Fin (k + 2)) ℚ) *
            (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
            (i.out : GL (Fin (k + 2)) ℚ)⁻¹) *
          diagMat (k + 2) (Fin.cons 1 c) ∈ (GL_pair (k + 2)).H) :
    ∃ N_i : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M_i, N_i, _M_X, _τ_X, _h_M_i_stab, h_int_conj, _h_block, _h_M_X_stab⟩ :=
    exists_stab_with_block_form_of_X_fiber a b c ha hb hc hda hdb i j hfib
  refine ⟨N_i, ?_⟩
  obtain ⟨ν, h_fib_GL⟩ := hfib_GL_eq a b c ha hb hc i j hfib
  have h_int_conj_GL := h_int_conj_GL_of_int_mat a ha M_i N_i h_int_conj
  exact jout_conj_N_i_stab_of_iMi_c_stab a b c ha hb hc i j M_i N_i ν
    h_fib_GL h_int_conj_GL (h_iMi_c_stab M_i)

/-- **T001 Layer 2 witness-specific bridge — corrected j-class upgrades to
canonical for a specific `(N_i, i_m, j_m)` tuple.**

Takes the explicit corrected-j tuple `(N_i, i_m, j_m)` as already produced by
`fiber_block_form_preimage_corrected_j_mulMap`, plus the **single witness-specific
hypothesis** that the j.out-conjugation of `mapGL ℚ N_i` is in the b-stabilizer.
Returns the canonical (i_m, j_m) package with full canonical class equalities
and `mulMap = ⟦diagMat_delta (k+1) c⟧`.

**Why witness-specific.**  The naive bare claim "if `N_i⁻¹` satisfies the
b-stabilizer condition" is mathematically incorrect: the canonical equality
`decompQuot_slSuccEmbed_diagMat b hb j_m = j` reduces (via `Quotient.sound` +
`mem_diagMat_cons_stabilizer_subgroupOf_iff`) to
`D_b⁻¹ · (j.out⁻¹ · mapGL ℚ N_i · j.out) · D_b ∈ H`, which is the j.out-twisted
form (subgroupOf D_b is not normal in H, so bare N_i stabilizer does not give
this).  This lemma exposes the precise required form as a single hypothesis;
the **universal-in-N_i version** (rejected by manager) was too strong.

**Use site (T001 ≤ direction).**  Combined with
`fiber_block_form_preimage_corrected_j_mulMap`, this gives the canonical
`(i_m, j_m)` + `mulMap` package needed by `heckeMultiplicity_block_embed_le_diagMat`.
The remaining T001 deliverable becomes producing the j.out-conjugated stabilizer
hypothesis for the **specific N_i** returned by the corrected descent — which
is a witness-specific algebraic fact derivable (in principle) from the
`D_a · N_i = M_i · D_a` integer-conjugate identity (`h_int_conj` in the
corrected_j output) plus the fiber equation. -/
private lemma fiber_block_form_preimage_canonical_j_witness_specific {k : ℕ}
    (a b : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b))
    (h_j_m_corrected :
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))))
    (h_jout_conj_N_i_stab :
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    decompQuot_slSuccEmbed_diagMat b hb j_m = j := by
  let _ := a
  let _ := ha
  rw [h_j_m_corrected]
  conv_rhs => rw [show j = ⟦j.out⟧ from (Quotient.out_eq j).symm]
  apply Quotient.sound
  change QuotientGroup.leftRel _
    ((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) * j.out)
    j.out
  rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
  have h_GL_val :
      (((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out)⁻¹ * j.out : (GL_pair (k + 2)).H) =
        ⟨(j.out : GL (Fin (k + 2)) ℚ)⁻¹ * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
            (j.out : GL (Fin (k + 2)) ℚ),
          (GL_pair (k + 2)).H.mul_mem
            ((GL_pair (k + 2)).H.mul_mem
              ((GL_pair (k + 2)).H.inv_mem j.out.2)
              (coe_mem_SLnZ (k + 2) N_i))
            j.out.2⟩ := by
    apply Subtype.ext
    show (((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
        j.out)⁻¹ * j.out : (GL_pair (k + 2)).H).val =
        (j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) * (j.out : GL (Fin (k + 2)) ℚ)
    push_cast
    rw [show (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ)⁻¹ from
        map_inv (mapGL ℚ : SpecialLinearGroup (Fin (k + 2)) ℤ →* _) N_i]
    group
  rw [h_GL_val]
  exact h_jout_conj_N_i_stab

/-- **T001 Layer 2 sufficiency consumer — existential j.out-conjugated stabilizer.**

Combines `fiber_block_form_preimage_corrected_j_mulMap` with the witness-specific
bridge `fiber_block_form_preimage_canonical_j_witness_specific` under the
existential premise `∃ N_i ..., (corrected output for N_i) ∧ (j.out-conjugated
stabilizer for N_i)`.

This phrases the rep-control bridge as an existential rather than a universal:
the hypothesis only needs to hold for the specific N_i produced by the corrected
descent, not for all N_i.  If a future worker can produce that single
witness-specific stabilizer (e.g. via the `D_a · N_i = M_i · D_a` integer-conjugate
identity and the fiber equation), this consumer immediately yields the canonical
`(i_m, j_m)` + `mulMap` package.

The hypothesis form `∃ N_i, (the corrected_j_mulMap output package for THAT N_i)
∧ (j.out-conj stab for THAT N_i)` is the **smallest sufficient existential
form** for the ≤ direction. -/
private lemma fiber_block_form_preimage_canonical_j_from_existential_witness {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (_ : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _))
    (h_witness_jout_conj_stab :
      ∃ (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
        (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
        (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
        decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
        decompQuot_slSuccEmbed_diagMat b hb j_m =
          (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
              j.out⟧ :
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
        HeckeRing.mulMap (GL_pair (k + 1))
            (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
          (⟦diagMat_delta (k + 1) c⟧ :
            HeckeRing.HeckeCoset (GL_pair (k + 1))) ∧
        (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
            (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
            (j.out : GL (Fin (k + 2)) ℚ)) *
          diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  let _ := hfib; let _ := hc; let _ := hda
  obtain ⟨N_i, i_m, j_m, h_i_m_canon, h_j_m_corrected, h_mulMap, h_stab⟩ :=
    h_witness_jout_conj_stab
  exact ⟨i_m, j_m, h_i_m_canon,
    fiber_block_form_preimage_canonical_j_witness_specific a b ha hb j N_i j_m
      h_j_m_corrected h_stab,
    h_mulMap⟩

/-- **i-side class-preimage bridge.** From `exists_stab_with_block_form_of_fiber`
(which produces `M ∈ stab` and `σ_m ∈ SL_(k+1)(ℤ)` with
`toSL i.out * M = slSuccEmbed σ_m`), construct the dim-(k+1) quotient class
`i_m := ⟦σ_m_H⟧` and prove `decompQuot_slSuccEmbed_diagMat a ha i_m = i`. The
proof shows the equivalence `slSuccEmbed_H σ_m_H ≈ i.out` reduces to the
in-stabilizer condition for `M⁻¹`, which follows from `M ∈ stab` plus subgroup
closure under inverses. -/
private lemma exists_i_m_block_class_eq_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i := by
  obtain ⟨M, σ_m, h_eq, h_M_stab⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  set σ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩
    with hσ_m_H_def
  refine ⟨⟦σ_m_H⟧, ?_⟩
  rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
  change ⟦slSuccEmbed_H σ_m_H⟧ = (⟦i.out⟧ : decompQuot _ _)
  apply Quotient.sound
  change QuotientGroup.leftRel _ (slSuccEmbed_H σ_m_H) i.out
  rw [QuotientGroup.leftRel_apply]
  rw [mem_diagMat_cons_stabilizer_subgroupOf_iff a ha]
  have h_toSL : toSL σ_m_H = σ_m := by
    apply mapGL_injective (k + 1)
    rw [toSL_spec]
  have h_GL_val :
      (((slSuccEmbed_H σ_m_H)⁻¹ * i.out : (GL_pair (k + 2)).H) :
        GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M)⁻¹ := by
    have h_slSuccEmbed_GL : (slSuccEmbed_H σ_m_H : GL (Fin (k + 2)) ℚ) =
        (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M := by
      show mapGL ℚ (slSuccEmbed (toSL σ_m_H)) = _
      rw [h_toSL, ← h_eq, map_mul, toSL_spec]
    push_cast
    rw [h_slSuccEmbed_GL]
    group
  rw [h_GL_val]
  have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
      ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by
    group
  rw [h_inv_form]
  exact inv_mem h_M_stab

/-- **Joint i/j class-preimage helper.** Symmetrising the i-side bridge
`exists_i_m_block_class_eq_of_fiber`, given block witnesses on BOTH sides
(`M_i, σ_m` for `i.out` and `M_j, τ_m` for `j.out`), produce the dim-(k+1)
quotient classes `i_m := ⟦σ_m_H⟧, j_m := ⟦τ_m_H⟧` that satisfy the two
`decompQuot_slSuccEmbed_diagMat` class equalities of
`fiber_has_block_form_preimages`. This is strictly stronger than the i-side-only
result: it produces both sides in a single sorry-free reduction.

The third conjunct of `fiber_has_block_form_preimages` (the lifted dim-(k+2)
mem_H for `slSuccEmbed_H i_m.out, slSuccEmbed_H j_m.out`) is NOT derivable from
independent i-side and j-side block witnesses because of a fundamental rep
dependence of the lifted mem_H expression under `Quotient.out`: replacing
`σ_m_H` with the canonical `i_m.out` introduces a stab_a (dim-(k+1)) factor
`t = σ_m_H⁻¹ * i_m.out` that, when transported through `D_a`, `slSuccEmbed_H τ_m_H`,
`D_b`, requires `σ_m_H * t * σ_m_H⁻¹ ∈ stab_c (dim-(k+1))`. For arbitrary
`(σ_m, τ_m, M_i, M_j)` this conjugation-into-stab_c condition fails (since
stab_a and stab_c differ when `a ≠ c`). The full lifted mem_H requires a
genuinely coordinated Smith-NF-style construction that simultaneously controls
the rep-difference behavior — this is the residual algebra blocker for
`fiber_has_block_form_preimages`. -/
private lemma fiber_class_preimages_from_joint_block_witnesses {k : ℕ}
    (a b : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_m)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_j : toSL j.out * M_j = slSuccEmbed τ_m)
    (h_stab_j : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j := by
  set σ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩
    with hσ_m_H_def
  set τ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩
    with hτ_m_H_def
  refine ⟨⟦σ_m_H⟧, ⟦τ_m_H⟧, ?_, ?_⟩
  · -- i-side class equality (mirrors `exists_i_m_block_class_eq_of_fiber`).
    rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    change ⟦slSuccEmbed_H σ_m_H⟧ = (⟦i.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H σ_m_H) i.out
    rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff a ha]
    have h_toSL_i : toSL σ_m_H = σ_m := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H σ_m_H)⁻¹ * i.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_i)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H σ_m_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_m_H)) = _
        rw [h_toSL_i, ← h_block_i, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_i
  · -- j-side class equality (mirror).
    rw [show j = ⟦j.out⟧ from (Quotient.out_eq j).symm]
    change ⟦slSuccEmbed_H τ_m_H⟧ = (⟦j.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H τ_m_H) j.out
    rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
    have h_toSL_j : toSL τ_m_H = τ_m := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H τ_m_H)⁻¹ * j.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_j)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H τ_m_H : GL (Fin (k + 2)) ℚ) =
          (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_j := by
        show mapGL ℚ (slSuccEmbed (toSL τ_m_H)) = _
        rw [h_toSL_j, ← h_block_j, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_j

/-- **Existential-rep form of `fiber_has_block_form_preimages`.** Given the
joint block witnesses (i-side and j-side together) AND the dim-(k+1) integer
matrix equation `h_joint`, produces `(i_m, j_m)` plus EXPLICIT existential
representatives `(rep_i = σ_m_H, rep_j = τ_m_H)` in the dim-(k+1) classes
satisfying the lifted dim-(k+2) mem_H for the SPECIFIC reps `σ_m_H, τ_m_H`
(not `Quotient.out i_m, Quotient.out j_m`).

This is strictly stronger than `fiber_class_preimages_from_joint_block_witnesses`
(which only produces the two class equalities) and is a clean reduction of
`fiber_has_block_form_preimages` to the **rep-control bridge** —
the precise named missing piece needed to bridge from `σ_m_H, τ_m_H` reps to
canonical `Quotient.out` reps. Specifically, the only remaining gap is:
given lifted mem_H for `(slSuccEmbed_H σ_m_H, slSuccEmbed_H τ_m_H)`, derive
lifted mem_H for `(slSuccEmbed_H i_m.out, slSuccEmbed_H j_m.out)` where
`i_m = ⟦σ_m_H⟧, j_m = ⟦τ_m_H⟧`. This bridge is rep-dependent under
`Quotient.out` and refuted by the dim-2 counterexample at
`a = (1, 4), c = (1, 8), t = [[1, 0], [4, 1]]` (Round 4 analysis), so it
genuinely requires either a coordinated Smith-NF construction or a refactor
of the abstract `heckeMultiplicity` to use existential reps. -/
private lemma fiber_has_block_form_preimages_existential_reps {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_m)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_j : toSL j.out * M_j = slSuccEmbed τ_m)
    (h_stab_j : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H)
    (h_joint : (diagMat (k + 1) c)⁻¹ *
      ((⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩ : (GL_pair (k + 1)).H) :
        GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) a *
      ((⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩ : (GL_pair (k + 1)).H) :
        GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) b ∈ (GL_pair (k + 1)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b))
      (rep_i : (GL_pair (k + 1)).H) (rep_j : (GL_pair (k + 1)).H),
      (⟦rep_i⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i_m ∧
      (⟦rep_j⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) = j_m ∧
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H rep_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H rep_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  set σ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩
    with hσ_m_H_def
  set τ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩
    with hτ_m_H_def
  refine ⟨⟦σ_m_H⟧, ⟦τ_m_H⟧, σ_m_H, τ_m_H, rfl, rfl, ?_, ?_, ?_⟩
  · -- i-side class equality.
    rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    change ⟦slSuccEmbed_H σ_m_H⟧ = (⟦i.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H σ_m_H) i.out
    rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff a ha]
    have h_toSL_i : toSL σ_m_H = σ_m := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H σ_m_H)⁻¹ * i.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_i)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H σ_m_H : GL (Fin (k + 2)) ℚ) =
          (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
        show mapGL ℚ (slSuccEmbed (toSL σ_m_H)) = _
        rw [h_toSL_i, ← h_block_i, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_i
  · -- j-side class equality (mirror).
    rw [show j = ⟦j.out⟧ from (Quotient.out_eq j).symm]
    change ⟦slSuccEmbed_H τ_m_H⟧ = (⟦j.out⟧ : decompQuot _ _)
    apply Quotient.sound
    change QuotientGroup.leftRel _ (slSuccEmbed_H τ_m_H) j.out
    rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
    have h_toSL_j : toSL τ_m_H = τ_m := by
      apply mapGL_injective (k + 1); rw [toSL_spec]
    have h_GL_val :
        (((slSuccEmbed_H τ_m_H)⁻¹ * j.out : (GL_pair (k + 2)).H) :
          GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ M_j)⁻¹ := by
      have h_slSuccEmbed_GL : (slSuccEmbed_H τ_m_H : GL (Fin (k + 2)) ℚ) =
          (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_j := by
        show mapGL ℚ (slSuccEmbed (toSL τ_m_H)) = _
        rw [h_toSL_j, ← h_block_j, map_mul, toSL_spec]
      push_cast
      rw [h_slSuccEmbed_GL]; group
    rw [h_GL_val]
    have h_inv_form : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b))⁻¹ := by group
    rw [h_inv_form]; exact inv_mem h_stab_j
  · -- The lifted dim-(k+2) mem_H for (slSuccEmbed_H σ_m_H, slSuccEmbed_H τ_m_H)
    exact slSuccEmbed_H_fiber_transfer a b c ha hb hc σ_m_H τ_m_H h_joint

/-- **Combinatorial core of Shimura L.3.19**: every fiber pair at dim `k+2` with
`Fin.cons 1 _` diagonals has dim-`k+1` class preimages under the
`decompQuot_slSuccEmbed_diagMat` block embedding, and moreover the lifted
mem_H condition at dim `k+2` holds for `slSuccEmbed_H i_m.out` and
`slSuccEmbed_H j_m.out`. The lifted mem_H is exactly what
`slSuccEmbed_H_fiber_transfer_converse` consumes, so
`fiber_block_form_preimage` reduces cleanly to this helper plus a single
application of the converse fiber transfer.

The hypothesis `hk : 1 ≤ k` is required: at `k = 0` (dim 2 → dim 1) the
conclusion is mathematically false — explicit counterexample
`A_i = [[1, 0], [2, 1]]`, `A_j = [[1, 0], [1, 1]]`, `ν = [[1, 0], [1, 1]]`,
`a = b = (2)`, `c = (4)` satisfies `hfib` but `[A_j] ≠ [I]` in `SL(2, ℤ) / Γ_0(2)`
while the only image of `decompQuot_slSuccEmbed_diagMat` from the trivial
dim-1 quotient is `[I]`. The downstream user
`heckeMultiplicity_block_embed` imposes `2 ≤ m`, which forces `k ≥ 1`. -/
private lemma fiber_has_block_form_preimages {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H i_m.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H j_m.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  sorry

/-- `fiber_block_form_preimage` follows from `fiber_has_block_form_preimages`:
the first two conjuncts are the class-match identities, and the third (dim-`k+1`
fiber condition) follows by applying `slSuccEmbed_H_fiber_transfer_converse`
to the lifted mem_H hypothesis and re-packaging via `fiber_diagMat_iff_mem_H`.
Inherits the `hk : 1 ≤ k` restriction from `fiber_has_block_form_preimages`. -/
private lemma fiber_block_form_preimage {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      ({(i_m.out : GL (Fin (k + 1)) ℚ) *
          (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
        {(j_m.out : GL (Fin (k + 1)) ℚ) *
          (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
        ((GL_pair (k + 1)).H : Set _) =
      {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
        ((GL_pair (k + 1)).H : Set _) := by
  obtain ⟨i_m, j_m, h1, h2, h_lifted⟩ :=
    fiber_has_block_form_preimages hk a b c ha hb hc hda hdb hdc i j hfib
  refine ⟨i_m, j_m, h1, h2, ?_⟩
  have h_k1_mem := slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc
    i_m.out j_m.out h_lifted
  have h_dval_a : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  simpa only [h_dval_a, h_dval_b, h_dval_c] using
    (fiber_diagMat_iff_mem_H a b c ha hb hc i_m.out j_m.out).mpr h_k1_mem

/-- **Diagonal-level ≤ direction of `heckeMultiplicity_block_embed`.** Injection
`Fiber_{k+2}^{cons1} → Fiber_{k+1}` built from `fiber_block_form_preimage` and
`decompQuot_slSuccEmbed_diagMat_injective`. Inherits the `hk : 1 ≤ k` restriction
from `fiber_block_form_preimage`. -/
private lemma heckeMultiplicity_block_embed_le_diagMat {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) := by
  let SrcType : Type := {p : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 a)) ×
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)) |
            ({(p.1.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) ×
            decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b) |
            ({(p.1.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
            ((GL_pair (k + 1)).H : Set _) =
            {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
              ((GL_pair (k + 1)).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hfib⟩ ↦
    let spec := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i j hfib
    let i_m := spec.choose
    let spec' := spec.choose_spec
    let j_m := spec'.choose
    ⟨(i_m, j_m), spec'.choose_spec.2.2⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, hfib₁⟩ ⟨⟨i₂, j₂⟩, hfib₂⟩ heq
  set spec₁ := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i₁ j₁ hfib₁ with hspec₁
  set spec₂ := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i₂ j₂ hfib₂ with hspec₂
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : spec₁.choose = spec₂.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : spec₁.choose_spec.choose = spec₂.choose_spec.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_spec_i₁ : decompQuot_slSuccEmbed_diagMat a ha spec₁.choose = i₁ :=
    spec₁.choose_spec.choose_spec.1
  have h_spec_j₁ : decompQuot_slSuccEmbed_diagMat b hb spec₁.choose_spec.choose = j₁ :=
    spec₁.choose_spec.choose_spec.2.1
  have h_spec_i₂ : decompQuot_slSuccEmbed_diagMat a ha spec₂.choose = i₂ :=
    spec₂.choose_spec.choose_spec.1
  have h_spec_j₂ : decompQuot_slSuccEmbed_diagMat b hb spec₂.choose_spec.choose = j₂ :=
    spec₂.choose_spec.choose_spec.2.1
  have h_i_final : i₁ = i₂ := by
    rw [← h_spec_i₁, ← h_spec_i₂, h_i_eq]
  have h_j_final : j₁ = j₂ := by
    rw [← h_spec_j₁, ← h_spec_j₂, h_j_eq]
  exact Subtype.ext (Prod.ext h_i_final h_j_final)

/-- **Hybrid `≤` direction with mulMap-form target.** Same source predicate as
`heckeMultiplicity_block_embed_le_diagMat` (set-form `heckeMultiplicity` at
dim `k+2`), but the dim-`(k+1)` target count is the rep-invariant
`heckeMultiplicityMulMap` form. Proof: chain the existing `_le_` direction with
the forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`.

This is the **forward-compatible API** for downstream consumers that can accept
the target-side count in the mulMap form.  The reverse hybrid direction
(mulMap-form on the source side) is not currently provided: the
`heckeMultiplicity_le_heckeMultiplicityMulMap` bridge is one-way only, so going
mulMap → set-form would require an additional compensation construction that is
not part of this API.

Inherits the `fiber_has_block_form_preimages` sorry from the source `_le_`
direction; no new sorries are introduced here.

**Recommended replacement.**  Downstream consumers that wish a sorry-free
proof of the same statement should use
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree`
(declared later in this file).  That public theorem delivers the same
inequality via Route A's direct chain (`_via_iFunctional` (T197) +
explicit corrected-j chain (T199) + `N_of_i_default` (T204)), bypassing
the `fiber_has_block_form_preimages` sorry entirely.  It preserves this
lemma's signature for drop-in substitution. -/
lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) :=
  le_trans
    (heckeMultiplicity_block_embed_le_diagMat hk a b c ha hb hc hda hdb hdc)
    (HeckeRing.heckeMultiplicity_le_heckeMultiplicityMulMap (GL_pair (k + 1))
      (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c))

/-- **Hybrid `≥` direction with mulMap-form target.** Same source predicate as
`heckeMultiplicity_block_embed_ge_diagMat` (set-form `heckeMultiplicity` at
dim `k+1`), but the dim-`(k+2)` target count is the rep-invariant
`heckeMultiplicityMulMap` form. Proof: chain the existing `_ge_` direction with
the forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`.

Sorry-free: the underlying `_ge_` direction is sorry-free (compensated injection
via `coset_shift_fwd_q1`), and the bridge is sorry-free. -/
lemma heckeMultiplicity_block_embed_ge_diagMat_target_mulMap {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  le_trans
    (heckeMultiplicity_block_embed_ge_diagMat a b c ha hb hc)
    (HeckeRing.heckeMultiplicity_le_heckeMultiplicityMulMap (GL_pair (k + 2))
      (diagMat_delta (k + 2) (Fin.cons 1 a))
      (diagMat_delta (k + 2) (Fin.cons 1 b))
      (diagMat_delta (k + 2) (Fin.cons 1 c)))

/-- **T001 consumer theorem: target-mulMap reduction of the block-embed
multiplicity goal at the diagMat level.**

Packages both target-mulMap hybrid directions (`_le_target_mulMap` and
`_ge_target_mulMap`) into a single statement: the block-embed `heckeMultiplicity`
at dim `(k+1)` and dim `(k+2)` are mutually bounded by the `heckeMultiplicityMulMap`
counts on the opposite side.  This is the strongest packaged statement currently
available without the converse `heckeMultiplicityMulMap → heckeMultiplicity`
direction; downstream consumers that can target-relax to the mulMap form get this
sandwich for free.

Inherits the existing `fiber_has_block_form_preimages` sorry only via the `_le_`
direction; the `_ge_` direction is sorry-free.

**Recommended replacement.**  Downstream consumers that need the same
sandwich without the sorry inheritance should use
`heckeMultiplicity_block_embed_target_mulMap_sandwich_sorryFree`
(declared later in this file). That theorem packages the same statement
but routes the `≤` direction through Route A's direct chain
(`_via_iFunctional` (T197) + explicit corrected-j chain (T199) +
`N_of_i_default` (T204)), eliminating the `fiber_has_block_form_preimages`
sorry entirely.  It preserves this theorem's full signature for drop-in
substitution.  -/
theorem heckeMultiplicity_block_embed_target_mulMap_sandwich {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ∧
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  ⟨heckeMultiplicity_block_embed_le_diagMat_target_mulMap hk a b c ha hb hc hda hdb hdc,
   heckeMultiplicity_block_embed_ge_diagMat_target_mulMap a b c ha hb hc⟩

/-- **Route A: ≤_diagMat target-mulMap reduction to an i-functional `N_i` extractor.**

Provides a sorry-free proof of the dim-(k+2) → dim-(k+1) `heckeMultiplicity` ≤
`heckeMultiplicityMulMap` inequality, *parameterized* by an `N_of_i` function
returning the conjugating SL element of the corrected-j descent at every fiber
pair, plus a hypothesis `h_iFunctional` asserting that the corrected-j chain's
output uses this specific `N_of_i i` (rather than a `(j, hfib)`-dependent choice).

**Why this is Route A's smallest sufficient form.**  T187 found that canonical
`Quotient.out` j-side col-divisibility is class-non-invariant, so directly
closing `fiber_has_block_form_preimages` is provably impossible without a
refactor that avoids `Quotient.out` rep choice on the j-side.  The corrected-j
chain (`fiber_block_form_preimage_corrected_j_mulMap`, sorry-free) provides the
rep-invariant `mulMap` data, but its `N_i` output is extracted from a
`(j, hfib)`-dependent existential and may differ across `(j, hfib)` pairs
sharing the same `i`.  The injection from the dim-(k+2) fiber set into the
dim-(k+1) `mulMap` fiber set (via `(i, j) ↦ (i_m, j_m)`) is injective IFF
`N_i` depends only on `i` — exactly what `h_iFunctional` captures.

**Closing `h_iFunctional` (remaining work).**  An i-functional `N_of_i` is
obtained by `Classical.choose` on the i-only existentials
`exists_stab_with_block_form_of_fiber` (i-only body) and
`exists_stab_int_conjugate_diagMat_cons_one` (i-only body given `M_i`).  By
Lean 4's proof irrelevance, both `Classical.choose` calls give i-functional
values.  The remaining work to *land* `h_iFunctional` sorry-free is to
refactor the corrected-j chain (`fiber_int_mat_eq_via_i_block`, `_rearr`,
`_rearr_adj`, `hfib_col_div_b_via_i_block`,
`fiber_block_form_preimage_corrected_j`, and `_mulMap`) to take
`(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)` as **explicit** inputs
(instead of extracting them via the j-dependent combined existential), so
that the chain's `N_i` matches the i-functional `Classical.choose`-extracted
one. Estimated ~700 LOC parameterization across the chain.

**Use site.**  Combined with the existing
`heckeMultiplicity_block_embed_ge_diagMat_target_mulMap` (sorry-free) and the
forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`, this closes the
target-mulMap sandwich at dim `(k+1)` and dim `(k+2)` without going through
the canonical `j.out`-divisibility chain at all. -/
private lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional
    {k : ℕ} (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (N_of_i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) →
              SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_iFunctional :
      ∀ (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
        (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
        (_hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
            (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(j.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)),
        ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
          (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
          decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
          decompQuot_slSuccEmbed_diagMat b hb j_m =
            (⟦(⟨mapGL ℚ (N_of_i i)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i)⁻¹⟩ :
                (GL_pair (k + 2)).H) * j.out⟧ :
              decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
          HeckeRing.mulMap (GL_pair (k + 1))
              (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
            (⟦diagMat_delta (k + 1) c⟧ :
              HeckeRing.HeckeCoset (GL_pair (k + 1)))) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) := by
  let _ := hda; let _ := hdb; let _ := hc
  let SrcType : Type := { p : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 a)) ×
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)) |
            ({(p.1.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _) }
  let MulMapTgtType : Type := { p : decompQuot (GL_pair (k + 1))
            (diagMat_delta (k + 1) a) ×
            decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b) |
            HeckeRing.mulMap (GL_pair (k + 1))
                (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨p.1, p.2⟩ =
              (⟦diagMat_delta (k + 1) c⟧ : HeckeRing.HeckeCoset (GL_pair (k + 1))) }
  let f : SrcType → MulMapTgtType := fun ⟨⟨i, j⟩, hfib⟩ ↦
    let spec := h_iFunctional i j hfib
    let i_m := spec.choose
    let spec' := spec.choose_spec
    let j_m := spec'.choose
    ⟨(i_m, j_m), spec'.choose_spec.2.2⟩
  simp only [HeckeRing.heckeMultiplicity, HeckeRing.heckeMultiplicityMulMap]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, hfib₁⟩ ⟨⟨i₂, j₂⟩, hfib₂⟩ heq
  set spec₁ := h_iFunctional i₁ j₁ hfib₁ with hspec₁
  set spec₂ := h_iFunctional i₂ j₂ hfib₂ with hspec₂
  have heq_pair := Subtype.mk.inj heq
  have h_i_m_eq : spec₁.choose = spec₂.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_m_eq : spec₁.choose_spec.choose = spec₂.choose_spec.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_canon₁ : decompQuot_slSuccEmbed_diagMat a ha spec₁.choose = i₁ :=
    spec₁.choose_spec.choose_spec.1
  have h_j_corr₁ :
      decompQuot_slSuccEmbed_diagMat b hb spec₁.choose_spec.choose =
        (⟦(⟨mapGL ℚ (N_of_i i₁)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₁)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₁.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) :=
    spec₁.choose_spec.choose_spec.2.1
  have h_i_canon₂ : decompQuot_slSuccEmbed_diagMat a ha spec₂.choose = i₂ :=
    spec₂.choose_spec.choose_spec.1
  have h_j_corr₂ :
      decompQuot_slSuccEmbed_diagMat b hb spec₂.choose_spec.choose =
        (⟦(⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₂.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) :=
    spec₂.choose_spec.choose_spec.2.1
  have h_i_final : i₁ = i₂ := by
    rw [← h_i_canon₁, ← h_i_canon₂, h_i_m_eq]
  have h_j_final : j₁ = j₂ := by
    have h_class_eq :
        (⟦(⟨mapGL ℚ (N_of_i i₁)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₁)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₁.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
        ⟦(⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₂.out⟧ := by
      rw [← h_j_corr₁, ← h_j_corr₂, h_j_m_eq]
    rw [h_i_final] at h_class_eq
    rw [Quotient.eq] at h_class_eq
    rw [QuotientGroup.leftRel_apply] at h_class_eq
    have h_simp :
        ((⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₁.out)⁻¹ *
        ((⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₂.out) =
        (j₁.out)⁻¹ * j₂.out := by
      group
    rw [h_simp] at h_class_eq
    rw [show j₁ = ⟦j₁.out⟧ from (Quotient.out_eq j₁).symm,
        show j₂ = ⟦j₂.out⟧ from (Quotient.out_eq j₂).symm]
    apply Quotient.sound
    change QuotientGroup.leftRel _ (Quotient.out j₁) (Quotient.out j₂)
    rw [QuotientGroup.leftRel_apply]
    exact h_class_eq
  exact Subtype.ext (Prod.ext h_i_final h_j_final)

/-- **i-only block-witness existence proposition.**

Asserts the existence of an i-side block-reduction triple
`(M, σ_m, N)` satisfying:

* `toSL i.out * M = slSuccEmbed σ_m` (block form);
* `M ∈ stab(D_a)` at the GL level (cons-1 stabilizer);
* `D_a · N = M · D_a` over ℤ (integer-conjugate identity).

The proposition mentions only `(a, ha, i)` — no `b, c, j, hfib` — making
it manifestly i-only.  By Lean 4's proof irrelevance, `Classical.choose`
on this proposition gives values that depend only on `(a, ha, i)`. -/
private def IBlockWitnessExists {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) :
    Prop :=
  ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ),
    toSL i.out * M = slSuccEmbed σ_m ∧
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
    Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N.val =
      M.val *
      Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))

/-- **`IBlockWitnessExists` is provable from any fiber pair `(j, hfib)`.**

Combines `exists_stab_with_block_form_of_fiber` (i-side block) and
`exists_stab_int_conjugate_diagMat_cons_one` (integer conjugate) to
construct the i-only existential witness. -/
private lemma iBlockWitnessExists_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    IBlockWitnessExists a ha i := by
  obtain ⟨M, σ_m, h_block, h_stab⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M h_stab
  exact ⟨M, σ_m, N, h_block, h_stab, h_int_conj⟩

/-- **Default i-functional `N_of_i` extractor.**

Selects the third component (`N`) of the i-only Classical.choose witness
for `IBlockWitnessExists`, falling back to `1` when the existential fails
(which happens only for `i` outside the image of any fiber, where the
count contributes nothing).

By construction, this is a function of `(a, ha, i)` alone — i-functional
in the sense required by
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`. -/
private noncomputable def N_of_i_default {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  classical
  exact if h : IBlockWitnessExists a ha i
  then h.choose_spec.choose_spec.choose
  else 1

/-- **Closed-form `_le_diagMat` target-mulMap inequality (Route A complete,
DIRECT proof — no `fiber_has_block_form_preimages` sorry inheritance).**

Combines `heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`
(T197) with the explicit corrected-j chain (T199) and the i-only
`Classical.choose` extraction of `N_of_i_default` (this ticket) to close
the dim-(k+2) → dim-(k+1) `heckeMultiplicity` ≤ `heckeMultiplicityMulMap`
inequality without any parameterized hypotheses.

**Why a separate `_direct` lemma.**  The pre-existing
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap` (line 8977) is a
hybrid: it chains `heckeMultiplicity_block_embed_le_diagMat` (which still
contains the architectural-blocker sorry at `fiber_has_block_form_preimages`)
with the rep-invariance bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`,
inheriting the sorry as a result.  This `_direct` variant bypasses the
sorry-bearing `_le_diagMat` step entirely by going through the
explicit-chain route, so it requires no `hk : 1 ≤ k` and no `hdc` (which
were artifacts of the sorry-bearing chain).

**Proof outline.**  Apply `_via_iFunctional` with `N_of_i_default a ha`,
reducing to `h_iFunctional`.  For each fiber pair `(i, j, hfib)`:

1. Establish `IBlockWitnessExists a ha i` from the fiber via
   `iBlockWitnessExists_of_fiber`.
2. By `dif_pos`, `N_of_i_default a ha i` unfolds to
   `h_iF.choose_spec.choose_spec.choose` for any proof `h_iF`.
3. Extract the i-functional `(M, σ, N)` triple plus its i-only conditions
   from `h_iF`.
4. Apply `fiber_block_form_preimage_corrected_j_mulMap_explicit` with
   these specific witnesses.

The key `i`-functionality argument is Lean 4's proof irrelevance: any two
proofs of `IBlockWitnessExists a ha i` are equal as elements of `Prop`,
hence `Classical.choose` gives the same value regardless of how the proof
was constructed (in particular, regardless of which `(j, hfib)` was used). -/
private lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct
    {k : ℕ} (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) := by
  refine heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional
    a b c ha hb hc hda hdb (N_of_i_default a ha) ?_
  intro i j hfib
  have h_iF : IBlockWitnessExists a ha i :=
    iBlockWitnessExists_of_fiber a b c ha hb hc hda i j hfib
  have h_N_def :
      N_of_i_default a ha i = h_iF.choose_spec.choose_spec.choose := by
    classical
    show (if h : IBlockWitnessExists a ha i
          then h.choose_spec.choose_spec.choose else 1) = _
    rw [dif_pos h_iF]
  set M_i : SpecialLinearGroup (Fin (k + 2)) ℤ := h_iF.choose with hM_i_def
  set σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ :=
    h_iF.choose_spec.choose with hσ_i_def
  set N_i : SpecialLinearGroup (Fin (k + 2)) ℤ :=
    h_iF.choose_spec.choose_spec.choose with hN_i_def
  have h_block_i : toSL i.out * M_i = slSuccEmbed σ_i :=
    h_iF.choose_spec.choose_spec.choose_spec.1
  have h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
    h_iF.choose_spec.choose_spec.choose_spec.2.1
  have h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) :=
    h_iF.choose_spec.choose_spec.choose_spec.2.2
  have h_N_eq : N_of_i_default a ha i = N_i := h_N_def.trans hN_i_def.symm
  rw [h_N_eq]
  exact fiber_block_form_preimage_corrected_j_mulMap_explicit a b c ha hb hc
    hdb i M_i σ_i h_block_i h_stab_i N_i h_int_conj j hfib

/-- **Public sorry-free target-mulMap `≤` direction (Route A).**

Public alias for the closed-form
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct` that
preserves the original sorry-inheriting hybrid's
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap` signature
(`hk`, `hdc` retained as no-op parameters for signature compatibility).
Downstream consumers that wish to use the sorry-free Route A proof
without touching the canonical `fiber_has_block_form_preimages` blocker
should call this theorem (or its no-`hk`/`hdc` analog
`_le_diagMat_target_mulMap_direct`) instead of the original hybrid.

The two `_` parameters (`_hk`, `_hdc`) are intentionally unused: the
direct Route A proof — built on `_via_iFunctional` (T197), the
explicit corrected-j chain (T199), and the i-functional `N_of_i_default`
extractor (T204) — does not require either `hk : 1 ≤ k` (the
`fiber_block_form_preimage` k=0 exclusion was an artifact of the
canonical-rep chain, not of Route A) or `hdc` (the `c` divisor chain
was used only for the canonical `_le_diagMat`'s sorry'd preimage step). -/
lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree
    {k : ℕ} (_hk : 1 ≤ k) (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (_hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) :=
  heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct
    a b c ha hb hc hda hdb

/-- **Public sorry-free target-mulMap sandwich theorem (Route A).**

Public sorry-free analog of `heckeMultiplicity_block_embed_target_mulMap_sandwich`
combining `_le_diagMat_target_mulMap_sorryFree` (this ticket) with the
existing sorry-free `_ge_diagMat_target_mulMap`.  Carries the original
sandwich's full signature for compatibility but routes the `≤` direction
through Route A's direct chain, **eliminating the
`fiber_has_block_form_preimages` sorry inheritance** that the original
sandwich theorem still carried via the canonical `_le_diagMat` route.

This is the recommended public API for downstream consumers that need
the dim-(k+1)/dim-(k+2) target-mulMap sandwich at the diagMat level
without entanglement to the architectural-blocker canonical j-side
divisibility chain (T187/T191/T195). -/
theorem heckeMultiplicity_block_embed_target_mulMap_sandwich_sorryFree
    {k : ℕ} (hk : 1 ≤ k) (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ∧
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  ⟨heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree hk a b c ha hb hc
      hda hdb hdc,
   heckeMultiplicity_block_embed_ge_diagMat_target_mulMap a b c ha hb hc⟩

/-- **Generic block-form witness from column-zero divisibility.**

Given any `Y ∈ SL(k+2, ℤ)` together with a `DivChain b` and the column-zero
divisibility `b r ∣ (Y⁻¹).val r.succ 0` (the "j-side col-divisibility"
hypothesis), produces `M ∈ SL(k+2, ℤ)` and `τ ∈ SL(k+1, ℤ)` such that:

* `Y * M = slSuccEmbed τ` (block form: first row/column of `Y · M` are
  `e_0` / `e_0^T`; bottom-right block is `τ`);
* `(diagMat (k+2) (Fin.cons 1 b))⁻¹ · mapGL ℚ M · diagMat (k+2) (Fin.cons 1 b)
  ∈ (GL_pair (k+2)).H` (`b`-stabilizer condition).

Mirrors the i-side construction `exists_stab_with_block_form_of_fiber` but
parameterized by an arbitrary `Y` and an arbitrary col-divisibility hypothesis,
making the generic block-reduction step independent of the fiber context.  Uses
`sl_first_col_primitive` (always-applicable primitivity from `Y⁻¹ ∈ SL`) and
`sl_exists_col_stab_divChain` (already proved) for the first column reduction;
then `sl_first_row_clear_with_col0_e0` for the first row clearance.

This is the natural reusable form: applying with `Y := toSL i.out` and
`hfib_col_div_a` recovers `exists_stab_with_block_form_of_fiber`'s i-side
output; applying with `Y := toSL j.out` and a hypothetical `hfib_col_div_b`
delivers the missing j-side block-form witness. -/
private lemma exists_stab_block_form_of_col_div {k : ℕ}
    (b : Fin (k + 1) → ℕ) (hb : ∀ i, 0 < b i) (hdb : DivChain (k + 1) b)
    (Y : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col_div_b : ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        (Y⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0) :
    ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ : SpecialLinearGroup (Fin (k + 1)) ℤ),
      Y * M = slSuccEmbed τ ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2),
          d ∣ (Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0) → IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (Y⁻¹) d hd
  obtain ⟨M_0, hM_0_col, hM_0_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_col_div_b
  have h_col_e0 : ∀ r : Fin (k + 2),
      (Y * M_0).val r 0 =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    have h_to_inv :
        (Y * M_0).val r 0 =
          (Y * Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      rw [hM_0_col p]
    rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (Y * M_0) h_col_e0 Finset.univ
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0 * T_clear with hM_def
  set N_full : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (Y * M).val with hN_def
  have hM_assoc : Y * M = (Y * M_0) * T_clear := by
    rw [hM_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N_full r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (Y * M).val r 0 = _
    rw [hM_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N_full 0 l.succ = 0 := by
    intro l
    show (Y * M).val 0 l.succ = _
    rw [hM_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N_full 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N_full I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set τ_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N_full I.succ J.succ with hτ_raw_def
  have h_det : τ_raw.det = 1 := by
    have h_det_N : N_full.det = 1 := by
      rw [hN_def]; exact (Y * M).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N_full 0 j.succ *
            (N_full.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero,
      hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat :
        N_full.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_raw := by
      ext I J
      show N_full I.succ ((0 : Fin (k + 2)).succAbove J) = τ_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set τ : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_raw, h_det⟩ with hτ_def
  have h_block : Y * M = slSuccEmbed τ := by
    apply Subtype.ext
    ext I J
    show N_full I J = (slSuccEmbed τ).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  have h_M_stab : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
    have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) =
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ M_0 : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) *
        ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 b)) := by
      rw [hM_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_stab hT_stab
  exact ⟨M, τ, h_block, h_M_stab⟩

/-- **j-side block-form witness, conditional on `hfib_col_div_b`.**

Specializes the generic block-form helper `exists_stab_block_form_of_col_div`
to `Y := toSL j.out`, packaging the missing j-side col-divisibility input
`b r ∣ ((toSL j.out)⁻¹).val r.succ 0` as an explicit hypothesis.

This is the **conditional** form of the j-side block witness referred to in
the architectural-blocker docblock below: with the col-divisibility supplied,
the rest of the construction (Bezout column reduction + first-row clearance +
stabilizer closure) goes through generically.

The remaining open question is whether `b r ∣ ((toSL j.out)⁻¹).val r.succ 0`
can be **proved** from the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`).  See the docblock below
for the structural asymmetry obstruction; see `hfib_col_div_b_canonical_stmt`
for the smallest precise missing arithmetic statement. -/
private lemma exists_stab_with_block_form_of_fiber_j_side_of_col_div {k : ℕ}
    (b : Fin (k + 1) → ℕ) (hb : ∀ i, 0 < b i) (hdb : DivChain (k + 1) b)
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (h_col_div_b : ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        ((toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0) :
    ∃ (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL j.out * M_j = slSuccEmbed τ_m ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H :=
  exists_stab_block_form_of_col_div b hb hdb (toSL j.out) h_col_div_b

/-- **Smallest precise missing arithmetic input for the j-side block witness.**

Statement of the col-zero divisibility on `(toSL j.out)⁻¹` that, together with
the existing i-side col-divisibility `hfib_col_div_a`, would supply the j-side
block-form witness `exists_stab_with_block_form_of_fiber_j_side_of_col_div`
unconditionally.

**Open status.**  This statement is the smallest precise mathematical
question whose resolution would mechanically discharge the j-side block
witness.  It is currently UNRESOLVED: the standard adjugate technique used to
prove `hfib_col_div_a` (premultiply by `adjugate A_i` and postmultiply by
`adjugate ν`) does NOT yield the analog for `(toSL j.out)⁻¹`.  Specifically,
the adjugate of the rearranged equation
`A_i · D_a · A_j · D_b = D_c · ν` gives
`adj D_b · adj A_j · adj D_a · adj A_i = adj ν · adj D_c`, and applying mulVec
on `e_0` produces an integer identity of the form
`γ · (adj A_j) r.succ 0 = b_r · Z_r` (where `Z_r ∈ ℤ` and `γ = ∏ c_q`).
This says `b_r ∣ γ · (adj A_j) r.succ 0`, but does **not** strip `γ` to
yield `b_r ∣ (adj A_j) r.succ 0` — `gcd(γ, b_r)` is not generally `1`, so the
divisibility may be entirely absorbed by the `γ` factor.

**Resolution paths beyond `T001`'s adjugate-only toolchain:**
1. A coordinated Smith-normal-form argument tracking `D_a · A_j · D_b`'s
   invariant factors against `D_c · ν` simultaneously, producing a
   "two-sided" block reduction of `A_j` against `D_b` (rather than only
   the "one-sided" reduction of `A_i` against `D_a`).
2. A lattice-theoretic descent isolating the column space of `A_j` modulo
   the `b`-summand of the dim-`(k+2)` lattice, exploiting the `Fin.cons 1`
   constraint on the leading entry of `D_b`.

Both routes require infrastructure beyond `BlockBijection.lean`'s current
scope (e.g. either `Mathlib.LinearAlgebra.Matrix.SmithNormalForm` over `ℤ`
specialized to non-PID-flat divisor chains, or a custom lattice descent
formalization).  -/
private def hfib_col_div_b_canonical_stmt : Prop :=
  ∀ {k : ℕ} (a b c : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hb : ∀ i, 0 < b i)
    (_hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (_hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)),
    ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        ((toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0

/-! ### Architectural blocker: missing j-side block-form witness from fiber

The `_le_diagMat` direction's underlying sorry (`fiber_has_block_form_preimages`)
goes through canonical `Quotient.out` representatives, and the rep-control bridge
from existential reps to canonical reps is rep-dependent (refuted by the dim-2
counterexample `a = (1, 4), c = (1, 8), t = [[1, 0], [4, 1]]` documented at
`fiber_has_block_form_preimages_existential_reps`).  An alternative sorry-free
proof path through `fiber_has_block_form_preimages_existential_reps` requires
**both** an i-side block-form witness (provided by
`exists_stab_with_block_form_of_fiber`) and a j-side analog.  The j-side analog
is currently missing; its precise required statement is:

```
private lemma exists_stab_with_block_form_of_fiber_j_side {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL j.out * M_j = slSuccEmbed τ_m ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H
```

**Why current APIs do not supply this.**  The i-side proof
(`exists_stab_with_block_form_of_fiber`) extracts column-zero divisibility
`a r ∣ (toSL i.out)⁻¹ r.succ 0` from the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`) by premultiplying by
`adjugate A_i` and postmultiplying by `adjugate ν`, which cancels `A_i` and `ν`
and isolates the desired column.  The same argument template applied to extract
`b r ∣ (toSL j.out)⁻¹ r.succ 0` runs into structural asymmetry:

* Transposing the equation to `D_b · A_j^T · D_a · A_i^T = ν^T · D_c` produces
  the form `D · A · D · A`, not the `A · D · A · D = D · M` form that the
  template requires (the leading factor on the LHS is now a diagonal `D_b`,
  whose adjugate is also diagonal and does not cancel cleanly into a row-extraction
  identity).
* Inverting the equation to isolate `A_j⁻¹` produces `A_j⁻¹ = D_b · ν⁻¹ · D_c⁻¹ · A_i · D_a`
  over `ℚ`; the `D_c⁻¹` factor is non-integer in general, so the resulting
  expression for column 0 of `A_j⁻¹` is `b'_r · (rational expression)`, which
  forces integer-divisibility of `(A_j⁻¹) r.succ 0` by `b r` only modulo
  divisibility constraints that are not immediate from `hfib`.

The structural asymmetry is intrinsic: `i.out` appears at the leftmost position
of the product `i.out · D_a · j.out · D_b`, with `D_a` immediately on its right;
`j.out` appears in the interior, with both `D_a` and `D_b` adjacent.  Extracting
"first-column divisibility of the inverse" from each factor therefore requires
asymmetric algebraic manipulations.

**Resolution paths (out of T001 prototype scope):**
1. A coordinated Smith-normal-form construction simultaneously block-reducing
   both `i.out` and `j.out` against `D_a, D_b, D_c, ν`, exploiting the cons-1
   constraint on the leading diagonal entries.
2. A lattice-theoretic argument projecting the dim-`(k+2)` fiber pair onto a
   dim-`(k+1)` sublattice via the ℤu_0-summand decomposition, recovering both
   block witnesses from a single lattice-level descent.

Either route yields the j-side block witness, which combined with the existing
i-side witness feeds `fiber_has_block_form_preimages_existential_reps` and
discharges the residual sorry. -/

lemma heckeMultiplicity_block_embed [NeZero (m + 1)]
    (a b c : Fin m → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain m a) (hdb : DivChain m b) (hdc : DivChain m c) (hm : 2 ≤ m) :
    HeckeRing.heckeMultiplicity (GL_pair (m + 1))
      (HeckeCoset.rep (T_diag (Fin.cons 1 a)))
      (HeckeCoset.rep (T_diag (Fin.cons 1 b)))
      (HeckeCoset.rep (T_diag (Fin.cons 1 c))) =
    HeckeRing.heckeMultiplicity (GL_pair m)
      (HeckeCoset.rep (T_diag a))
      (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag c)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have bridge_m := heckeMultiplicity_rep_eq_diagMat_delta (n := k + 1) a b c ha hb hc
  have bridge_m1 := heckeMultiplicity_rep_eq_diagMat_delta (n := k + 2)
    (Fin.cons 1 a) (Fin.cons 1 b) (Fin.cons 1 c) hcons_a hcons_b hcons_c
  rw [bridge_m1, bridge_m]
  exact le_antisymm
    (heckeMultiplicity_block_embed_le_diagMat (k := k) hk a b c ha hb hc hda hdb hdc)
    (heckeMultiplicity_block_embed_ge_diagMat (k := k) a b c ha hb hc)

end HeckeRing.GLn
