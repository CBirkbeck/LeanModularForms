/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.CharSpaceIso

/-!
# Bridge: `heckeT_p` on `modFormCharSpace k 1` corresponds to `heckeOperator_Gamma0`

This file shows that on the trivial-character eigenspace `modFormCharSpace k 1`,
the Γ₁(N)-level Hecke operator `heckeT_p` corresponds (via the canonical isomorphism
`modFormCharSpace_one_equiv_Gamma0`) to the Γ₀(N)-level abstract Hecke operator
`heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)`.

## Main theorem

* `heckeT_p_val_eq_heckeOperator_Gamma0_on_charSpace_one` — for
  `f ∈ modFormCharSpace k 1`, the two operators agree as functions `ℍ → ℂ`.

## Strategy

1. (Internal) `tRep_gen_D_p_Gamma0_matches_T_p_reps`: Γ₀(N)-analogue of the level-1
   matching `tRep_gen_D_p_matches_T_p_reps`, using a bijection built from the
   Phase 1 cardinality and the Phase 3 distinctness lemmas from `HeckeT_p_Gamma0.lean`.
   For a `Γ₀(N)`-invariant function, the abstract sum equals the explicit `T_p`
   formula `∑ b < p, f ∣[k] T_p_upper(b) + f ∣[k] T_p_lower`.

2. Combine with `heckeT_p_fun_eq_coset_sum` (which expresses `heckeT_p_fun` in terms of
   the upper sum plus `f ∣[k] M_∞`) and the diamond identity
   `slash_M_infty_eq_diamond_slash_T_p_lower`. For `f ∈ modFormCharSpace k 1`, the
   diamond twist vanishes (`⟨p⟩ f = f`), so `f ∣[k] M_∞ = f ∣[k] T_p_lower`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### Γ₀(N)-invariance helpers for `f ∈ modFormCharSpace k 1` -/

/-- For `f : modFormCharSpace k 1`, the underlying function is Γ₀(N)-slash-invariant
via `glMap`. This is the invariance hypothesis required by `heckeSlash_gen`. -/
private lemma charSpaceOne_Gamma0_pair_H_invariant (k : ℤ)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ∀ h, h ∈ (Gamma0_pair N).H →
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) ∣[k] glMap h =
        ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  intro h hh
  -- View `(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)` as a function that equals
  -- the Γ₀(N)-form produced by `modFormCharSpace_one_equiv_Gamma0`.
  set g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k :=
    modFormCharSpace_one_equiv_Gamma0 N k f
  have hfg : ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = ⇑g := by rfl
  rw [hfg]
  exact Gamma0_pair_H_invariant_of_invariant N
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ) h hh

/-- For `f ∈ modFormCharSpace k 1`, every diamond operator acts trivially. -/
private lemma diamondOp_trivial_of_charSpaceOne (k : ℤ)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (d : (ZMod N)ˣ) :
    diamondOp k d (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have := (mem_modFormCharSpace_iff k (1 : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mp f.property d
  simpa using this

/-! ### Adjugate factorisations and the key `slash` identity for Γ₀(N)

These mimic the level-1 private lemmas in `HeckeT_p_GLpair.lean`. -/

/-- Matrix identity `adj(diag(1, p)) = T_p_lower p`. -/
private lemma adj_diag_1p_eq_T_p_lower_bridge (p : ℕ) (hp : Nat.Prime p) :
    GL_adjugate (diagMat 2 ![1, p] : GL (Fin 2) ℚ) =
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
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
      Matrix.of_apply, huniv, he0, he1, Finset.prod_singleton]

/-- `adj(rep(D_p_Gamma0)) ∈ D_p_Gamma0`. -/
private lemma adj_rep_mem_D_p_Gamma0_bridge (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) ∈
      HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  have hrep := HeckeCoset.rep_mem (D_p_Gamma0 N p hp.pos)
  rw [D_p_Gamma0, diag_1p_delta_Gamma0, HeckeCoset.toSet_mk,
    DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  have hTl := T_p_lower_mem_D_p_Gamma0 N p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨b₁, hb₁, b₂, hb₂, hTl_eq⟩ := hTl
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  refine ⟨GL_adjugate c * b₁,
    (Gamma0_pair N).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hb₁,
    b₂ * GL_adjugate a,
    (Gamma0_pair N).H.mul_mem hb₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  have h1 : GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      GL_adjugate c * GL_adjugate (diagMat 2 ![1, p]) * GL_adjugate a := by
    conv_lhs => rw [show (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      a * diagMat 2 ![1, p] * c from hrep_eq]
    rw [GL_adjugate_mul, GL_adjugate_mul, mul_assoc]
  rw [h1, adj_diag_1p_eq_T_p_lower_bridge p hp, hTl_eq]; group

/-- Generic: if `adj(rep) ∈ D` then `adj` preserves `D`. -/
private lemma GL_adjugate_mem_D_p_Gamma0_bridge (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (g : GL (Fin 2) ℚ)
    (hg : g ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos)) :
    GL_adjugate g ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  have hadj_rep := adj_rep_mem_D_p_Gamma0_bridge p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg hadj_rep ⊢
  obtain ⟨a, ha, c, hc, heq⟩ := hg
  obtain ⟨r₁, hr₁, r₂, hr₂, hrep_eq⟩ := hadj_rep
  refine ⟨GL_adjugate c * r₁,
    (Gamma0_pair N).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hr₁,
    r₂ * GL_adjugate a,
    (Gamma0_pair N).H.mul_mem hr₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  rw [heq, GL_adjugate_mul, GL_adjugate_mul]
  rw [show GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
    r₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * r₂ from hrep_eq]
  group

/-- For any `g ∈ D_p_Gamma0` and Γ₀(N)-invariant `f`, there exists a `decompQuot`
element `σ` with `f ∣[k] g = f ∣[k] tRep_gen σ`, and a factorisation of `adj(g)`. -/
private lemma adj_mem_dc_factorisation_Gamma0_bridge (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (g : GL (Fin 2) ℚ)
    (hg : g ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos)) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate g =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ := by
  have hadj_mem := GL_adjugate_mem_D_p_Gamma0_bridge p hp hpN g hg
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hadj_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hadj_mem
  exact ⟨h₁, hh₁, h₂, hh₂, heq⟩

/-- Γ₀(N)-level `slash_eq_tRep_gen_of_adj_mem`: if `adj(g) = h₁ * rep * h₂` with
`h₁, h₂ ∈ (Gamma0_pair N).H` and `f` is `(Gamma0_pair N).H`-invariant, then
`f ∣[k] g = f ∣[k] tRep_gen (Gamma0_pair N) D ⟦⟨h₁, hh₁⟩⟧`. -/
private lemma slash_eq_tRep_gen_of_adj_mem_Gamma0_bridge (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f)
    (D : HeckeCoset (Gamma0_pair N))
    (g : GL (Fin 2) ℚ) (h₁ h₂ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (Gamma0_pair N).H) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hadj : GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    f ∣[k] g = f ∣[k] tRep_gen (Gamma0_pair N) D ⟦⟨h₁, hh₁⟩⟧ := by
  have hg : g = GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) := by
    rw [← hadj, GL_adjugate_involutive]
  rw [hg]
  exact slash_tRep_gen_of_mem k D h₁ h₂ hh₁ hh₂ f hf

/-- If `g₁, g₂` both admit adjugate factorisations `adj(gᵢ) = hᵢ * rep(D) * h'ᵢ`
through `D` whose left factors are equal in the decomposition quotient
`decompQuot (Gamma0_pair N) (rep D)`, then `(adj g₁)⁻¹ * adj g₂ ∈ (Gamma0_pair N).H`.
This is the algebraic core of the injectivity of the rep-matching map. -/
private lemma adj_inv_mul_mem_H_of_factorisations_Gamma0_bridge
    (D : HeckeCoset (Gamma0_pair N)) (g₁ g₂ : GL (Fin 2) ℚ)
    (e₁ : ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
      (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate g₁ = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (e₂ : ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
      (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate g₂ = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (hquot : (⟦⟨e₁.choose, e₁.choose_spec.choose⟩⟧ :
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) =
      ⟦⟨e₂.choose, e₂.choose_spec.choose⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (Gamma0_pair N).H := by
  rw [e₁.choose_spec.choose_spec.choose_spec.choose_spec,
    e₂.choose_spec.choose_spec.choose_spec.choose_spec]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf] at hrel
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at hrel
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  set a₁ := e₁.choose
  set c₁ := e₁.choose_spec.choose_spec.choose
  set a₂ := e₂.choose
  set c₂ := e₂.choose_spec.choose_spec.choose
  have h_prod : (a₁ * ↑(HeckeCoset.rep D) * c₁)⁻¹ *
      (a₂ * ↑(HeckeCoset.rep D) * c₂) =
      c₁⁻¹ * ((↑(HeckeCoset.rep D))⁻¹ * (a₁⁻¹ * a₂) *
        ↑(HeckeCoset.rep D)) * c₂ := by group
  rw [h_prod]
  exact (Gamma0_pair N).H.mul_mem
    ((Gamma0_pair N).H.mul_mem
      ((Gamma0_pair N).H.inv_mem e₁.choose_spec.choose_spec.choose_spec.choose) hrel)
    e₂.choose_spec.choose_spec.choose_spec.choose

/-! ### The matching theorem at `Γ₀(N)` — inline construction of the bijection

This mirrors the level-1 `tRep_gen_D_p_matches_T_p_reps` but works at level Γ₀(N),
using the Γ₀(N) distinctness lemmas. We rebuild the bijection inline (rather than
calling `T_p_coset_reps_Gamma0_equiv`) so that definitional equalities go through. -/

/-- The map `Fin (p+1) → decompQuot` built from adjugate factorisations of the
classical `T_p` representatives: `b < p` maps to the upper coset of `T_p_upper b`,
and the top index maps to the lower coset of `T_p_lower`. -/
private noncomputable def phiOfFactorisations_Gamma0_bridge (p : ℕ)
    (hp : Nat.Prime p) (D : HeckeCoset (Gamma0_pair N))
    (h_upper_dc : ∀ b : Fin p,
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
        (_ : h₂ ∈ (Gamma0_pair N).H),
        GL_adjugate (T_p_upper p hp.pos b.val : GL _ ℚ) =
          h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (h_lower_dc : ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
      (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
        h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    Fin (p + 1) → decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := fun j =>
  if h : j.val < p then
    ⟦⟨(h_upper_dc ⟨j.val, h⟩).choose, (h_upper_dc ⟨j.val, h⟩).choose_spec.choose⟩⟧
  else
    ⟦⟨h_lower_dc.choose, h_lower_dc.choose_spec.choose⟩⟧

/-- The map `phiOfFactorisations_Gamma0_bridge` matches the classical `T_p`
representatives under slashing: the explicit `T_p_upper`/`T_p_lower` slash equals
the abstract `tRep_gen` slash at `φ j`, for any `(Gamma0_pair N).H`-invariant `f`. -/
private lemma phiOfFactorisations_slash_eq_tRep_gen_Gamma0_bridge (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f)
    (h_upper_dc : ∀ b : Fin p,
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
        (_ : h₂ ∈ (Gamma0_pair N).H),
        GL_adjugate (T_p_upper p hp.pos b.val : GL _ ℚ) =
          h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (h_lower_dc : ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
      (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
        h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) (j : Fin (p + 1)) :
    (if _h : j.val < p then f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ)
      else f ∣[k] (T_p_lower p hp.pos : GL _ ℚ)) =
    f ∣[k] tRep_gen (Gamma0_pair N) D
      (phiOfFactorisations_Gamma0_bridge p hp D h_upper_dc h_lower_dc j) := by
  simp only [phiOfFactorisations_Gamma0_bridge]
  split_ifs with h
  · exact slash_eq_tRep_gen_of_adj_mem_Gamma0_bridge k f hf D _ _ _
      (h_upper_dc ⟨j.val, h⟩).choose_spec.choose
      (h_upper_dc ⟨j.val, h⟩).choose_spec.choose_spec.choose_spec.choose
      (h_upper_dc ⟨j.val, h⟩).choose_spec.choose_spec.choose_spec.choose_spec
  · exact slash_eq_tRep_gen_of_adj_mem_Gamma0_bridge k f hf D _ _ _
      h_lower_dc.choose_spec.choose
      h_lower_dc.choose_spec.choose_spec.choose_spec.choose
      h_lower_dc.choose_spec.choose_spec.choose_spec.choose_spec

/-- `phiOfFactorisations_Gamma0_bridge` is injective: distinct indices give distinct
cosets, using the Γ₀(N) distinctness lemmas (`adj_upper_inv_mul_not_mem_H` etc.)
combined with `Gamma0_pair_H_le_GL_pair_H`. -/
private lemma phiOfFactorisations_injective_Gamma0_bridge (p : ℕ) (hp : Nat.Prime p)
    (D : HeckeCoset (Gamma0_pair N))
    (h_upper_dc : ∀ b : Fin p,
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
        (_ : h₂ ∈ (Gamma0_pair N).H),
        GL_adjugate (T_p_upper p hp.pos b.val : GL _ ℚ) =
          h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (h_lower_dc : ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL _ ℚ)
      (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
        h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    Function.Injective
      (phiOfFactorisations_Gamma0_bridge p hp D h_upper_dc h_lower_dc) := by
  intro j₁ j₂ heq
  by_contra hne
  simp only [phiOfFactorisations_Gamma0_bridge] at heq
  by_cases h₁ : j₁.val < p <;> by_cases h₂ : j₂.val < p
  · -- Both upper.
    simp only [h₁, h₂, dite_true] at heq
    have hne_val : j₁.val ≠ j₂.val := fun h => hne (Fin.ext h)
    have hmem := adj_inv_mul_mem_H_of_factorisations_Gamma0_bridge D _ _
      (h_upper_dc ⟨j₁.val, h₁⟩) (h_upper_dc ⟨j₂.val, h₂⟩) heq
    exact HeckeRing.GL2.adj_upper_inv_mul_not_mem_H p hp j₁.val j₂.val h₁ h₂ hne_val
      (Gamma0_pair_H_le_GL_pair_H N hmem)
  · -- j₁ upper, j₂ lower.
    simp only [h₁, dite_true, h₂, dite_false] at heq
    have hmem := adj_inv_mul_mem_H_of_factorisations_Gamma0_bridge D _ _
      (h_upper_dc ⟨j₁.val, h₁⟩) h_lower_dc heq
    exact HeckeRing.GL2.adj_upper_inv_mul_lower_not_mem_H p hp j₁.val
      (Gamma0_pair_H_le_GL_pair_H N hmem)
  · -- j₁ lower, j₂ upper.
    simp only [h₁, dite_false, h₂, dite_true] at heq
    have hmem := adj_inv_mul_mem_H_of_factorisations_Gamma0_bridge D _ _
      h_lower_dc (h_upper_dc ⟨j₂.val, h₂⟩) heq
    exact HeckeRing.GL2.adj_lower_inv_mul_upper_not_mem_H p hp j₂.val
      (Gamma0_pair_H_le_GL_pair_H N hmem)
  · -- Both ≥ p, but Fin (p+1) forces equality.
    have := j₁.isLt; have := j₂.isLt; omega

/-- Γ₀(N)-level analogue of `tRep_gen_D_p_matches_T_p_reps`: for a `Γ₀(N)`-invariant
function `f : ℍ → ℂ`, the abstract `heckeSlash_gen` sum equals the explicit `T_p`
coset-sum formula. -/
theorem tRep_gen_D_p_Gamma0_matches_T_p_reps (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f) :
    ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)),
      f ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i =
    (∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set D := D_p_Gamma0 N p hp.pos with hD_def
  -- Adjugate factorisations for the p+1 classical reps.
  have h_upper_dc : ∀ b : Fin p,
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
        GL_adjugate (T_p_upper p hp.pos b.val : GL _ ℚ) =
          h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂ := fun b =>
    adj_mem_dc_factorisation_Gamma0_bridge p hp hpN _
      (T_p_upper_mem_D_p_Gamma0 N p hp b.val)
  have h_lower_dc :
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
        GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
          h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂ :=
    adj_mem_dc_factorisation_Gamma0_bridge p hp hpN _
      (T_p_lower_mem_D_p_Gamma0 N p hp hpN)
  -- The matching bijection `φ` and its value/injectivity properties (see helpers).
  set φ := phiOfFactorisations_Gamma0_bridge p hp D h_upper_dc h_lower_dc
  have h_val := phiOfFactorisations_slash_eq_tRep_gen_Gamma0_bridge k p hp D f hf
    h_upper_dc h_lower_dc
  have h_card :
      Fintype.card (decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) = p + 1 := by
    have h := HeckeCoset_deg_D_p_Gamma0 N p hp hpN
    rw [Nat.card_eq_fintype_card] at h; exact h
  have h_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨phiOfFactorisations_injective_Gamma0_bridge p hp D h_upper_dc h_lower_dc,
      by rw [Fintype.card_fin, h_card]⟩
  -- Rewrite the explicit T_p sum as a sum over Fin(p+1) via `dite`.
  symm
  rw [← Fin.sum_univ_eq_sum_range]
  rw [show (∑ j : Fin p, f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ)) +
      f ∣[k] (T_p_lower p hp.pos : GL _ ℚ) =
    ∑ j : Fin (p + 1),
      if h : j.val < p then f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ)
      else f ∣[k] (T_p_lower p hp.pos : GL _ ℚ) from by
    rw [Fin.sum_univ_castSucc]; congr 1
    · congr 1; ext j; simp [j.isLt]
    · simp]
  exact Fintype.sum_bijective φ h_bij _ _ h_val

/-! ### Main bridge theorem -/

/-- **Bridge theorem**: on `modFormCharSpace k 1`, the Γ₁(N)-level Hecke operator
`heckeT_p k p hp hpN f.val` agrees pointwise with the Γ₀(N)-level abstract Hecke
operator `heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)` composed with the
canonical isomorphism `modFormCharSpace_one_equiv_Gamma0`.

More precisely, as functions `ℍ → ℂ`:
```
heckeT_p_fun k p hp hpN f.val =
  heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) ↑f
```
which unfolds `heckeOperator_Gamma0`. -/
theorem heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p_fun k p hp hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos)
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  -- Step 1: LHS = `heckeT_p_ut + (⟨p⟩ f) ∣[k] T_p_lower`. Via `heckeT_p_fun_eq_coset_sum`,
  -- this is `heckeT_p_ut + f ∣[k] M_∞`.
  rw [heckeT_p_fun_eq_coset_sum k hp hpN (f : ModularForm _ k)]
  -- Step 2: `f ∣[k] M_∞ = f ∣[k] T_p_lower` via diamond triviality.
  have hdiamond := diamondOp_trivial_of_charSpaceOne (N := N) k f
    (ZMod.unitOfCoprime p hpN)
  have hM_inf_eq :
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) =
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    rw [slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN
      (f : ModularForm _ k)]
    rw [show ⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) from by rw [hdiamond]]
  rw [hM_inf_eq]
  -- Step 3: apply the matching theorem.
  unfold heckeSlash_gen
  rw [tRep_gen_D_p_Gamma0_matches_T_p_reps k p hp hpN _
    (charSpaceOne_Gamma0_pair_H_invariant k f)]
  simp only [heckeT_p_ut]

/-- **Main theorem**: on `modFormCharSpace k 1`, the Γ₁(N)-level Hecke operator
`heckeT_p` corresponds via `modFormCharSpace_one_equiv_Gamma0` to the Γ₀(N)-level
Hecke operator `heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)`.

Stated as equality of modular forms in `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
theorem heckeT_p_val_eq_heckeOperator_Gamma0_on_charSpace_one (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p k p hp hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ((modFormCharSpace_one_equiv_Gamma0 N k).symm
      (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
        (modFormCharSpace_one_equiv_Gamma0 N k f)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  apply ModularForm.ext
  intro z
  -- Unfold `heckeT_p` and the RHS to functions at `z`.
  show heckeT_p_fun k p hp hpN (f : ModularForm _ k) z =
    (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
      (modFormCharSpace_one_equiv_Gamma0 N k f) : ℍ → ℂ) z
  change heckeT_p_fun k p hp hpN (f : ModularForm _ k) z =
    heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos)
      (⇑(modFormCharSpace_one_equiv_Gamma0 N k f)) z
  -- The two coercions agree.
  have h_coe : ⇑(modFormCharSpace_one_equiv_Gamma0 N k f) =
      ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    funext w; rw [modFormCharSpace_one_equiv_Gamma0_apply]
  rw [h_coe]
  exact congr_fun (heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one k p hp hpN f) z

/-- Forward-direction variant: `heckeOperator_Gamma0 ∘ equiv = equiv ∘ heckeT_p`. -/
theorem heckeOperator_Gamma0_eq_equiv_heckeT_p_on_charSpace_one (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
      (modFormCharSpace_one_equiv_Gamma0 N k f) =
    modFormCharSpace_one_equiv_Gamma0 N k
      ⟨heckeT_p k p hp hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
        heckeT_p_preserves_modFormCharSpace k p hp hpN _ f.property⟩ := by
  apply ModularForm.ext
  intro z
  -- Pointwise: both functions equal `heckeT_p_fun ... z` by construction.
  show (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
      (modFormCharSpace_one_equiv_Gamma0 N k f) : ℍ → ℂ) z =
    (modFormCharSpace_one_equiv_Gamma0 N k
      ⟨heckeT_p k p hp hpN (f : ModularForm _ k),
        heckeT_p_preserves_modFormCharSpace k p hp hpN _ f.property⟩ : ℍ → ℂ) z
  change heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos)
      (⇑(modFormCharSpace_one_equiv_Gamma0 N k f)) z =
    heckeT_p_fun k p hp hpN (f : ModularForm _ k) z
  have h_coe : ⇑(modFormCharSpace_one_equiv_Gamma0 N k f) =
      ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    funext w; rw [modFormCharSpace_one_equiv_Gamma0_apply]
  rw [h_coe]
  exact (congr_fun (heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one k p hp hpN f)
    z).symm

end HeckeRing.GL2
