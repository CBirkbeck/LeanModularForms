/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Commutativity via Anti-Involution

Shimura Proposition 3.8: if an arithmetic group pair admits an anti-automorphism
`ι : G →* Gᵐᵒᵖ` that preserves H and Δ and fixes every double coset, then the
Hecke ring `𝕋 P ℤ` is commutative.
-/

open Commensurable Classical Doset MulOpposite Set DoubleCoset Subgroup Commensurable Finsupp

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (P : ArithmeticGroupPair G)

/-- An anti-involution of an ArithmeticGroupPair is an anti-automorphism `ι : G →* Gᵐᵒᵖ`
    that is involutive and preserves both H and Δ. The prototypical example is matrix
    transpose for GL_n. -/
structure AntiInvolution where
  toFun : G →* MulOpposite G
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  map_H : ∀ g, g ∈ P.H → (toFun g).unop ∈ P.H
  map_Δ : ∀ g, g ∈ P.Δ → (toFun g).unop ∈ P.Δ

variable {P}

namespace AntiInvolution

variable (ι : AntiInvolution P)

/-- The underlying function `G → G` that reverses multiplication. -/
def bar (g : G) : G := (ι.toFun g).unop

@[simp] lemma bar_bar (g : G) : ι.bar (ι.bar g) = g := ι.involutive g

lemma bar_mul (a b : G) : ι.bar (a * b) = ι.bar b * ι.bar a := by
  simp only [bar, map_mul, unop_mul]

lemma bar_one : ι.bar 1 = 1 := by simp [bar]

lemma bar_inv (g : G) : ι.bar g⁻¹ = (ι.bar g)⁻¹ := by simp [bar]

lemma bar_injective : Function.Injective ι.bar := by
  intro a b h
  have := congr_arg ι.bar h
  simp at this
  exact this

lemma bar_mem_H {g : G} (hg : g ∈ P.H) : ι.bar g ∈ P.H := ι.map_H g hg

lemma bar_mem_Δ {g : G} (hg : g ∈ P.Δ) : ι.bar g ∈ P.Δ := ι.map_Δ g hg

/-- `bar` preserves double cosets: if two elements represent the same double coset,
    then their images under `bar` also represent the same double coset. -/
lemma bar_doubleCoset_eq (g₁ g₂ : G) (h : DoubleCoset.doubleCoset g₁ P.H P.H =
    DoubleCoset.doubleCoset g₂ P.H P.H) :
    DoubleCoset.doubleCoset (ι.bar g₁) P.H P.H =
    DoubleCoset.doubleCoset (ι.bar g₂) P.H P.H := by
  have hmem := (DoubleCoset.eq P.H P.H _ _).mp (DoubleCoset.mk_eq_of_doubleCoset_eq h)
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := hmem
  -- g₂ = h₁ * g₁ * h₂, so bar(g₂) = bar(h₂) * bar(g₁) * bar(h₁)
  have hbar : ι.bar g₂ = ι.bar h₂ * ι.bar g₁ * ι.bar h₁ := by
    rw [hprod, bar_mul, bar_mul, mul_assoc]
  rw [hbar]; symm; rw [mul_assoc]
  trans (DoubleCoset.doubleCoset (ι.bar g₁ * ι.bar h₁) (P.H : Set G) P.H)
  · exact doset_mul_left_eq_self P ⟨ι.bar h₂, ι.bar_mem_H hh₂⟩ _
  · exact DoubleCoset.doubleCoset_mul_right_eq_self P ⟨ι.bar h₁, ι.bar_mem_H hh₁⟩ _

/-- The anti-involution induces a map on double cosets `T' P`. -/
noncomputable def onT' (D : T' P) : T' P :=
  T_mk P ⟨ι.bar (D.eql.choose : G), ι.bar_mem_Δ D.eql.choose.2⟩

lemma onT'_set (D : T' P) :
    (ι.onT' D).set = DoubleCoset.doubleCoset (ι.bar (D.eql.choose : G)) P.H P.H := rfl

lemma onT'_involutive : Function.Involutive ι.onT' := by
  intro D
  apply T'_ext P
  simp only [onT', T_mk]
  -- (onT' (onT' D)).set = doubleCoset (bar (choose of onT' D)) H H
  -- We need: this = D.set
  -- Step 1: (onT' D).eql.choose_spec gives:
  --   (onT' D).set = doubleCoset (choose of onT' D) H H
  -- Step 2: by definition, (onT' D).set = doubleCoset (bar (choose of D)) H H
  -- So: doubleCoset (choose of onT' D) H H = doubleCoset (bar (choose of D)) H H
  -- Step 3: by bar_doubleCoset_eq:
  --   doubleCoset (bar (choose of onT' D)) H H = doubleCoset (bar (bar (choose of D))) H H
  --                                              = doubleCoset (choose of D) H H  [by bar_bar]
  --                                              = D.set  [by D.eql.choose_spec]
  have h_onT'_spec := (ι.onT' D).eql.choose_spec
  rw [onT', T_mk] at h_onT'_spec
  simp only at h_onT'_spec
  -- h_onT'_spec : doubleCoset (bar (choose of D)) H H = doubleCoset (choose of onT' D) H H
  have h3 := ι.bar_doubleCoset_eq _ _ h_onT'_spec.symm
  simp only [bar_bar] at h3
  rw [h3]
  exact D.eql.choose_spec.symm

/-- Bar maps elements of a double coset into the same double coset (given h_fix). -/
private lemma bar_mem_doubleCoset (h_fix : ∀ D : T' P, ι.onT' D = D)
    (D₀ : T' P) (x : G) (hx : x ∈ D₀.set) : ι.bar x ∈ D₀.set := by
  have h_set : (ι.onT' D₀).set = D₀.set := congr_arg T'.set (h_fix D₀)
  rw [← h_set, onT'_set]
  rw [D₀.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hx
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := hx
  rw [hprod, DoubleCoset.mem_doubleCoset]
  exact ⟨ι.bar h₂, ι.bar_mem_H hh₂, ι.bar h₁, ι.bar_mem_H hh₁, by
    simp [bar_mul, mul_assoc]⟩

/-- Under h_fix, bar(g) ∈ HgH for any representative g of a double coset. -/
private lemma bar_choose_mem_doubleCoset (h_fix : ∀ D : T' P, ι.onT' D = D)
    (D : T' P) : ∃ h₁ h₂ : P.H,
    ι.bar (D.eql.choose : G) = h₁ * (D.eql.choose : G) * h₂ := by
  set g := (D.eql.choose : G)
  have hg_mem : g ∈ D.set := by
    rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self P.H P.H _
  have hbar : ι.bar g ∈ D.set := bar_mem_doubleCoset ι h_fix D g hg_mem
  rw [D.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hbar
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hbar
  exact ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, heq⟩


set_option maxHeartbeats 800000 in
private lemma m'_le_comm (h_fix : ∀ D : T' P, ι.onT' D = D)
    (D₁ D₂ D : T' P) : m' P D₁ D₂ D ≤ m' P D₂ D₁ D := by
  set g₁ := (D₁.eql.choose : G)
  set g₂ := (D₂.eql.choose : G)
  set g_D := (D.eql.choose : G)
  obtain ⟨h1D, h2D, hbarD⟩ := bar_choose_mem_doubleCoset ι h_fix D
  obtain ⟨h1₁, h2₁, hbar₁⟩ := bar_choose_mem_doubleCoset ι h_fix D₁
  obtain ⟨h1₂, h2₂, hbar₂⟩ := bar_choose_mem_doubleCoset ι h_fix D₂
  have hbarD' : ι.bar g_D = (h1D : G) * g_D * (h2D : G) := hbarD
  have hbar₁' : ι.bar g₁ = (h1₁ : G) * g₁ * (h2₁ : G) := hbar₁
  set q₀ : decompQuot P D := ⟦⟨(h1D : G), h1D.2⟩⟧
  unfold m'
  push_cast
  rw [← m'_uniform P D₂ D₁ D q₀]
  norm_cast
  have bar_mem_dc := bar_mem_doubleCoset ι h_fix
  -- Forward map (transparent `let`)
  let fwd : {⟨i, j⟩ : decompQuot P D₁ × decompQuot P D₂ |
      ({(i.out : G) * g₁} : Set G) * {(j.out : G) * g₂} * P.H =
      {g_D} * (P.H : Set G)} →
    {p : decompQuot P D₂ × decompQuot P D₁ |
      ({(p.1.out : G) * g₂} : Set G) * {(p.2.out : G) * g₁} * P.H =
      {(q₀.out : G) * g_D} * (P.H : Set G)} :=
    fun ⟨⟨i, j⟩, (hcond : _ = _)⟩ =>
    let x : G := g₁⁻¹ * (i.out : G)⁻¹ * g_D
    have hx_mem_D₂ : x ∈ D₂.set := by
      rw [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset]
      have hcond' : ({(i.out : G) * g₁} : Set G) * {(j.out : G) * g₂} * ↑P.H =
          {g_D} * ↑P.H := hcond
      have hmem : (i.out : G) * g₁ * ((j.out : G) * g₂) ∈ ({g_D} : Set G) * ↑P.H := by
        have h1 : (i.out : G) * g₁ * ((j.out : G) * g₂) ∈
            ({(i.out : G) * g₁} : Set G) * {(j.out : G) * g₂} * ↑P.H :=
          ⟨_, ⟨_, rfl, _, rfl, rfl⟩, 1, P.H.one_mem, mul_one _⟩
        rwa [hcond'] at h1
      obtain ⟨_, hd, k, hk, hprod⟩ := hmem
      rw [Set.mem_singleton_iff] at hd; subst hd
      have hprod' : g_D * k = (i.out : G) * g₁ * ((j.out : G) * g₂) := hprod
      refine ⟨(j.out : G), j.out.2, k⁻¹, P.H.inv_mem hk, ?_⟩
      calc g₁⁻¹ * (i.out : G)⁻¹ * g_D
          = g₁⁻¹ * (i.out : G)⁻¹ * ((i.out : G) * g₁ * ((j.out : G) * g₂) * k⁻¹) := by
            rw [show g_D = (i.out : G) * g₁ * ((j.out : G) * g₂) * k⁻¹ from by
              calc g_D = g_D * k * k⁻¹ := by group
                _ = _ := by rw [hprod']]
        _ = (j.out : G) * g₂ * k⁻¹ := by group
    have hbarx_mem_D₂ : ι.bar x ∈ D₂.set := bar_mem_dc D₂ x hx_mem_D₂
    have hbarx_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        ι.bar x = h₁ * g₂ * h₂ := by
      rwa [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hbarx_mem_D₂
    let a : P.H := ⟨hbarx_dc.choose, hbarx_dc.choose_spec.1⟩
    let j' : decompQuot P D₂ := ⟦a⟧
    let y : G := g₂⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * g_D
    let b_val : G := hbarx_dc.choose_spec.2.choose
    have hb : b_val ∈ (P.H : Set G) := hbarx_dc.choose_spec.2.choose_spec.1
    have hbarx_eq : ι.bar x = (a : G) * g₂ * b_val := hbarx_dc.choose_spec.2.choose_spec.2
    have hy_mem_D₁ : y ∈ D₁.set := by
      rw [D₁.eql.choose_spec]
      change y ∈ DoubleCoset.doubleCoset g₁ (P.H : Set G) P.H
      rw [DoubleCoset.mem_doubleCoset]
      have hbar_x_eq : ι.bar x = ι.bar g_D * (ι.bar (i.out : G))⁻¹ * (ι.bar g₁)⁻¹ := by
        show ι.bar (g₁⁻¹ * (i.out : G)⁻¹ * g_D) = _
        rw [ι.bar_mul, ι.bar_mul, ι.bar_inv, ι.bar_inv]; group
      have hab_eq : (a : G) * g₂ * b_val = ι.bar g_D * (ι.bar (i.out : G))⁻¹ * (ι.bar g₁)⁻¹ := by
        rw [← hbar_x_eq]; exact hbarx_eq.symm
      have key1 : g₂⁻¹ * (a : G)⁻¹ * ι.bar g_D = b_val * ι.bar g₁ * ι.bar (i.out : G) := by
        have := hab_eq
        calc g₂⁻¹ * (a : G)⁻¹ * ι.bar g_D
            = g₂⁻¹ * (a : G)⁻¹ * ((a : G) * g₂ * b_val * (ι.bar g₁ * ι.bar (i.out : G))) := by
              rw [this]; group
          _ = b_val * ι.bar g₁ * ι.bar (i.out : G) := by group
      have hq₀_coset : ∃ h' : P.H, (q₀.out : G) * g_D = ι.bar g_D * (h' : G) := by
        obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct g_D • P.H).subgroupOf P.H) ⟨(h1D : G), h1D.2⟩
        have hn_coe : (q₀.out : G) = (h1D : G) * (n : G) := by
          have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
          simpa [Subgroup.coe_mul] using this
        have hn_conj : g_D⁻¹ * (n : G) * g_D ∈ P.H := by
          have := n.2
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
            ConjAct.smul_def] at this
          simpa [ConjAct.ofConjAct_toConjAct] using this
        exact ⟨⟨(h2D : G)⁻¹ * (g_D⁻¹ * (n : G) * g_D),
          P.H.mul_mem (P.H.inv_mem h2D.2) hn_conj⟩, by
          rw [hn_coe, hbarD']; group⟩
      obtain ⟨h', hq₀_eq⟩ := hq₀_coset
      obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H) a
      have hn₂_coe : (j'.out : G) = (a : G) * (n₂ : G) := by
        have := congr_arg (Subtype.val : ↥P.H → G) hn₂_eq
        simpa [Subgroup.coe_mul] using this
      have hn₂_conj : g₂⁻¹ * (n₂ : G) * g₂ ∈ P.H := by
        have := n₂.2
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ConjAct.smul_def] at this
        simpa [ConjAct.ofConjAct_toConjAct] using this
      have hy_calc : y = (g₂⁻¹ * (n₂ : G)⁻¹ * g₂) *
          (b_val * ι.bar g₁ * ι.bar (i.out : G)) * (h' : G) := by
        show g₂⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * g_D = _
        rw [hn₂_coe]
        rw [show g₂⁻¹ * ((a : G) * (n₂ : G))⁻¹ * (q₀.out : G) * g_D =
          g₂⁻¹ * ((a : G) * (n₂ : G))⁻¹ * ((q₀.out : G) * g_D) from by group]
        rw [hq₀_eq, ← key1]; group
      rw [hy_calc, hbar₁']
      refine ⟨(g₂⁻¹ * (n₂ : G)⁻¹ * g₂) * b_val * h1₁,
        P.H.mul_mem (P.H.mul_mem (by convert P.H.inv_mem hn₂_conj using 1; group) hb)
          h1₁.2,
        h2₁ * ι.bar (i.out : G) * (h' : G),
        P.H.mul_mem (P.H.mul_mem h2₁.2 (ι.bar_mem_H i.out.2)) h'.2, ?_⟩
      group
    have hy_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        y = h₁ * g₁ * h₂ := by
      rwa [D₁.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hy_mem_D₁
    let c : P.H := ⟨hy_dc.choose, hy_dc.choose_spec.1⟩
    let i' : decompQuot P D₁ := ⟦c⟧
    (⟨⟨j', i'⟩, by
      show ({(j'.out : G) * g₂} : Set G) * {(i'.out : G) * g₁} * ↑P.H =
        {(q₀.out : G) * g_D} * ↑P.H
      rw [Set.singleton_mul_singleton]
      let d_val := hy_dc.choose_spec.2.choose
      have hd : d_val ∈ (P.H : Set G) := hy_dc.choose_spec.2.choose_spec.1
      have hy_eq : y = (c : G) * g₁ * d_val := hy_dc.choose_spec.2.choose_spec.2
      obtain ⟨n₁, hn₁_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₁ • P.H).subgroupOf P.H) c
      have hn₁_coe : (i'.out : G) = (c : G) * (n₁ : G) := by
        have := congr_arg (Subtype.val : ↥P.H → G) hn₁_eq
        simpa [Subgroup.coe_mul] using this
      have hn₁_conj : g₁⁻¹ * (n₁ : G) * g₁ ∈ P.H := by
        have := n₁.2
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ConjAct.smul_def] at this
        simpa [ConjAct.ofConjAct_toConjAct] using this
      apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
      refine ⟨(j'.out : G) * g₂ * ((i'.out : G) * g₁),
        ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
      have h_prod_eq : (j'.out : G) * g₂ * ((c : G) * g₁ * d_val) = (q₀.out : G) * g_D := by
        have : y = (c : G) * g₁ * d_val := hy_eq
        show (j'.out : G) * g₂ * ((c : G) * g₁ * d_val) = (q₀.out : G) * g_D
        have hy_def : y = g₂⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * g_D := rfl
        rw [← this, hy_def]; group
      refine ⟨d_val⁻¹ * (g₁⁻¹ * (n₁ : G) * g₁),
        P.H.mul_mem (P.H.inv_mem hd) hn₁_conj, ?_⟩
      simp only [smul_eq_mul]
      rw [hn₁_coe]
      calc (q₀.out : G) * g_D * (d_val⁻¹ * (g₁⁻¹ * (n₁ : G) * g₁))
          = ((q₀.out : G) * g_D * d_val⁻¹) * (g₁⁻¹ * (n₁ : G) * g₁) := by group
        _ = ((j'.out : G) * g₂ * ((c : G) * g₁)) * (g₁⁻¹ * (n₁ : G) * g₁) := by
            congr 1
            calc (q₀.out : G) * g_D * d_val⁻¹
                = (j'.out : G) * g₂ * ((c : G) * g₁ * d_val) * d_val⁻¹ := by
                  rw [h_prod_eq.symm]
              _ = (j'.out : G) * g₂ * ((c : G) * g₁) := by group
        _ = (j'.out : G) * g₂ * ((c : G) * (n₁ : G) * g₁) := by group
      ⟩ : {p : decompQuot P D₂ × decompQuot P D₁ |
      ({(p.1.out : G) * g₂} : Set G) * {(p.2.out : G) * g₁} * P.H =
      {(q₀.out : G) * g_D} * (P.H : Set G)})
  -- Injectivity of fwd.
  -- Strategy: extract components from heq using congr_arg (no unfolding),
  -- then use `change` to state what those components definitionally are.
  -- Since fwd is a `let`-binding, Lean can check def-eq without expanding in context.
  apply Nat.card_le_card_of_injective fwd
  intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
  -- Extract the two component equalities from heq via Subtype.ext + Prod.ext
  have heq_val := congr_arg Subtype.val heq
  have hj'_eq := congr_arg Prod.fst heq_val
  have hi'_eq := congr_arg Prod.snd heq_val
  -- Clear heq to prevent it from bloating the context
  clear heq heq_val
  -- The first components of the output are the j' values (decompQuot P D₂).
  -- By definition of fwd, j' = ⟦a⟧ where a = ⟨(bar x).dc.choose, ...⟩
  -- and x = g₁⁻¹ * i.out⁻¹ * g_D.
  -- We use `change` to tell Lean what hj'_eq actually says.
  -- Since fwd is transparent (let-bound), Lean verifies this is definitionally equal.
  have h₁' : ({(i₁.out : G) * g₁} : Set G) * {(j₁.out : G) * g₂} * ↑P.H =
      {g_D} * ↑P.H := h₁
  have h₂' : ({(i₂.out : G) * g₁} : Set G) * {(j₂.out : G) * g₂} * ↑P.H =
      {g_D} * ↑P.H := h₂
  -- Now prove i₁ = i₂ using the bar-based argument.
  -- We work with x₁, x₂ directly via `have` (not `set`, to avoid context traversal).
  have hi₁₂ : i₁ = i₂ := by
    -- The j' components are equal. By construction, j' depends on i through
    -- bar(g₁⁻¹ * i.out⁻¹ * g_D). Equal j' means a₁ and a₂ are in the same coset.
    -- We'll re-derive the key facts for x₁ and x₂ without using `set`.
    let x₁ : G := g₁⁻¹ * (i₁.out : G)⁻¹ * g_D
    let x₂ : G := g₁⁻¹ * (i₂.out : G)⁻¹ * g_D
    have hx₁_D₂ : x₁ ∈ D₂.set := by
      rw [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset]
      have hmem : (i₁.out : G) * g₁ * ((j₁.out : G) * g₂) ∈ ({g_D} : Set G) * ↑P.H := by
        have h1 : (i₁.out : G) * g₁ * ((j₁.out : G) * g₂) ∈
            ({(i₁.out : G) * g₁} : Set G) * {(j₁.out : G) * g₂} * ↑P.H :=
          ⟨_, ⟨_, rfl, _, rfl, rfl⟩, 1, P.H.one_mem, mul_one _⟩
        rwa [h₁'] at h1
      obtain ⟨_, hd, k, hk, hprod⟩ := hmem
      rw [Set.mem_singleton_iff] at hd; subst hd
      have hprod' : g_D * k = (i₁.out : G) * g₁ * ((j₁.out : G) * g₂) := hprod
      refine ⟨(j₁.out : G), j₁.out.2, k⁻¹, P.H.inv_mem hk, ?_⟩
      show g₁⁻¹ * (i₁.out : G)⁻¹ * g_D = _
      calc g₁⁻¹ * (i₁.out : G)⁻¹ * g_D
          = g₁⁻¹ * (i₁.out : G)⁻¹ * ((i₁.out : G) * g₁ * ((j₁.out : G) * g₂) * k⁻¹) := by
            rw [show g_D = (i₁.out : G) * g₁ * ((j₁.out : G) * g₂) * k⁻¹ from by
              calc g_D = g_D * k * k⁻¹ := by group
                _ = _ := by rw [hprod']]
        _ = (j₁.out : G) * g₂ * k⁻¹ := by group
    have hbarx₁_D₂ : ι.bar x₁ ∈ D₂.set := bar_mem_dc D₂ x₁ hx₁_D₂
    have hbarx₁_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        ι.bar x₁ = h₁ * g₂ * h₂ := by
      rwa [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hbarx₁_D₂
    let a₁ : P.H := ⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩
    let b₁_val : G := hbarx₁_dc.choose_spec.2.choose
    have hb₁ : b₁_val ∈ (P.H : Set G) := hbarx₁_dc.choose_spec.2.choose_spec.1
    have hbarx₁_eq : ι.bar x₁ = (a₁ : G) * g₂ * b₁_val :=
      hbarx₁_dc.choose_spec.2.choose_spec.2
    have hx₂_D₂ : x₂ ∈ D₂.set := by
      rw [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset]
      have hmem : (i₂.out : G) * g₁ * ((j₂.out : G) * g₂) ∈ ({g_D} : Set G) * ↑P.H := by
        have h1 : (i₂.out : G) * g₁ * ((j₂.out : G) * g₂) ∈
            ({(i₂.out : G) * g₁} : Set G) * {(j₂.out : G) * g₂} * ↑P.H :=
          ⟨_, ⟨_, rfl, _, rfl, rfl⟩, 1, P.H.one_mem, mul_one _⟩
        rwa [h₂'] at h1
      obtain ⟨_, hd, k, hk, hprod⟩ := hmem
      rw [Set.mem_singleton_iff] at hd; subst hd
      have hprod' : g_D * k = (i₂.out : G) * g₁ * ((j₂.out : G) * g₂) := hprod
      refine ⟨(j₂.out : G), j₂.out.2, k⁻¹, P.H.inv_mem hk, ?_⟩
      show g₁⁻¹ * (i₂.out : G)⁻¹ * g_D = _
      calc g₁⁻¹ * (i₂.out : G)⁻¹ * g_D
          = g₁⁻¹ * (i₂.out : G)⁻¹ * ((i₂.out : G) * g₁ * ((j₂.out : G) * g₂) * k⁻¹) := by
            rw [show g_D = (i₂.out : G) * g₁ * ((j₂.out : G) * g₂) * k⁻¹ from by
              calc g_D = g_D * k * k⁻¹ := by group
                _ = _ := by rw [hprod']]
        _ = (j₂.out : G) * g₂ * k⁻¹ := by group
    have hbarx₂_D₂ : ι.bar x₂ ∈ D₂.set := bar_mem_dc D₂ x₂ hx₂_D₂
    have hbarx₂_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        ι.bar x₂ = h₁ * g₂ * h₂ := by
      rwa [D₂.eql.choose_spec, DoubleCoset.mem_doubleCoset] at hbarx₂_D₂
    let a₂ : P.H := ⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩
    let b₂_val : G := hbarx₂_dc.choose_spec.2.choose
    have hb₂ : b₂_val ∈ (P.H : Set G) := hbarx₂_dc.choose_spec.2.choose_spec.1
    have hbarx₂_eq : ι.bar x₂ = (a₂ : G) * g₂ * b₂_val :=
      hbarx₂_dc.choose_spec.2.choose_spec.2
    -- The key step: hj'_eq says the j' outputs are equal.
    -- By construction, fwd maps (i,j) to (j', i') where j' = ⟦a⟧ with a from bar(x).
    -- So hj'_eq tells us ⟦a₁⟧ = ⟦a₂⟧ in decompQuot P D₂.
    -- We extract the coset membership from hj'_eq.
    -- Since fwd is let-bound, (fwd ...).val.fst is definitionally ⟦a⟧.
    -- hj'_eq : (fwd src₁).val.fst = (fwd src₂).val.fst
    -- We use `change` to tell Lean this is an equality of quotient elements.
    change (⟦⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩⟧ : decompQuot P D₂) =
      ⟦⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩⟧ at hj'_eq
    rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj'_eq
    have ha_kernel : g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂ ∈ P.H := by
      have hmem := hj'_eq
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ConjAct.smul_def] at hmem
      simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
        Subgroup.coe_mul, Subgroup.coe_inv] at hmem
      have : g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂ =
          g₂⁻¹ * ((a₁ : G)⁻¹ * (a₂ : G)) * g₂ := by group
      rw [this]; exact hmem
    have hbar_diff : (ι.bar x₁)⁻¹ * ι.bar x₂ =
        b₁_val⁻¹ * (g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂) * b₂_val := by
      rw [hbarx₁_eq, hbarx₂_eq]; group
    have hbar_diff_H : (ι.bar x₁)⁻¹ * ι.bar x₂ ∈ P.H := by
      rw [hbar_diff]
      exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem hb₁) ha_kernel) hb₂
    have hbar_factor : (ι.bar x₁)⁻¹ * ι.bar x₂ = ι.bar (x₂ * x₁⁻¹) := by
      rw [← ι.bar_inv, ← ι.bar_mul]
    have hxx_H : x₂ * x₁⁻¹ ∈ P.H := by
      have hbar_mem := hbar_factor ▸ hbar_diff_H
      have := ι.bar_bar (x₂ * x₁⁻¹)
      rw [← this]
      exact ι.bar_mem_H hbar_mem
    have hxx_calc : x₂ * x₁⁻¹ = g₁⁻¹ * (i₂.out : G)⁻¹ * (i₁.out : G) * g₁ := by
      show (g₁⁻¹ * (i₂.out : G)⁻¹ * g_D) * (g₁⁻¹ * (i₁.out : G)⁻¹ * g_D)⁻¹ = _
      group
    have hconj_H : g₁⁻¹ * (i₂.out : G)⁻¹ * (i₁.out : G) * g₁ ∈ P.H :=
      hxx_calc ▸ hxx_H
    -- We need (i₁.out)⁻¹ * i₂.out in the conjugated subgroup, but hconj_H
    -- has i₂⁻¹ * i₁. Take the inverse.
    have hconj_H' : g₁⁻¹ * (i₁.out : G)⁻¹ * (i₂.out : G) * g₁ ∈ P.H := by
      have := P.H.inv_mem hconj_H
      convert this using 1; group
    rw [show i₁ = ⟦i₁.out⟧ from (Quotient.out_eq' i₁).symm,
        show i₂ = ⟦i₂.out⟧ from (Quotient.out_eq' i₂).symm]
    rw [@Quotient.eq'', QuotientGroup.leftRel_apply]
    show (i₁.out : ↥P.H)⁻¹ * i₂.out ∈ (ConjAct.toConjAct g₁ • P.H).subgroupOf P.H
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    convert hconj_H' using 1
    simp [Subgroup.coe_mul]; group
  subst hi₁₂
  have hj₁₂ : j₁ = j₂ := by
    by_contra hne
    apply decompQuot_coset_diff P D₂ j₁ j₂ hne
    have hcancel : ({(j₁.out : G) * g₂} : Set G) * ↑P.H =
        ({(j₂.out : G) * g₂} : Set G) * ↑P.H := by
      have h12 := h₁'.trans h₂'.symm
      rw [mul_assoc, mul_assoc] at h12
      exact set_singleton_mul_left_cancel ((i₁.out : G) * g₁) h12
    exact hcancel
  subst hj₁₂; rfl

/-- Shimura Proposition 3.8: m'(D₁, D₂, D) = m'(D₂, D₁, D) when bar fixes all double cosets.
    Proved by applying `m'_le_comm` in both directions and using `le_antisymm`. -/
lemma m'_comm_of_onT'_eq (h_fix : ∀ D : T' P, ι.onT' D = D)
    (D₁ D₂ D : T' P) : m' P D₁ D₂ D = m' P D₂ D₁ D :=
  le_antisymm (ι.m'_le_comm h_fix D₁ D₂ D) (ι.m'_le_comm h_fix D₂ D₁ D)

/-- If `ι` fixes every double coset, the multiplicity finsupps commute. -/
lemma m_comm_of_onT'_eq (h_fix : ∀ D : T' P, ι.onT' D = D)
    (D₁ D₂ : T' P) : m P D₁ D₂ = m P D₂ D₁ := by
  ext D
  simp only [m, Finsupp.coe_mk]
  exact m'_comm_of_onT'_eq ι h_fix D₁ D₂ D

/-- If `ι` fixes every double coset, multiplication in the Hecke ring is commutative. -/
theorem mul_comm_of_antiInvolution (h_fix : ∀ D : T' P, ι.onT' D = D)
    (f g : 𝕋 P ℤ) : f * g = g * f := by
  apply 𝕋.induction_linear P f
  · simp
  · intro D₁ a
    apply 𝕋.induction_linear P g
    · simp
    · intro D₂ b
      rw [T_single_mul_T_single, T_single_mul_T_single, m_comm_of_onT'_eq ι h_fix]
      rw [show a • b • m P D₂ D₁ = b • a • m P D₂ D₁ from by rw [smul_comm]]
    · intro g₁ g₂ hg₁ hg₂
      rw [mul_add, add_mul, hg₁, hg₂]
  · intro f₁ f₂ hf₁ hf₂
    rw [add_mul, mul_add, hf₁, hf₂]

end AntiInvolution

/-- Shimura Proposition 3.8: if the arithmetic group pair admits an anti-involution
    fixing every double coset, then the Hecke ring is a commutative ring. -/
noncomputable def instCommRing_of_antiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : T' P, ι.onT' D = D) :
    CommRing (𝕋 P ℤ) :=
  { HeckeRing.instRing P with
    mul_comm := ι.mul_comm_of_antiInvolution h_fix }

end HeckeRing
