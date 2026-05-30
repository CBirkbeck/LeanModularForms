/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334
import Mathlib.Data.ZMod.Units

/-!
# Prop 3.34 — Stabilizer surjectivity on diamond characters

For `g ∈ Δ₀(N)` with `gcd(det g, N) = 1`, the stabilizer subgroup
`(ConjAct g • (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H` maps surjectively onto
`(ZMod N)ˣ` under `Gamma0MapUnits`. This is a key step for the preservation of
`modFormCharSpace k χ` under `heckeSlash_gen` (Prop 3.34-E).

## Main results

* `Gamma0MapUnits_surjOn_stab_diag` — surjectivity for the diagonal case `g = diag(1, k)`,
  the case used by `heckeT_p` for `p` coprime to `N`.
* `Gamma0MapUnits_surjOn_stab_transport` — transports stabilizer surjectivity across the
  `Γ₀(N)`-double coset action, using abelianness of `(ZMod N)ˣ`.
* `Gamma0MapUnits_surjOn_stab_of_diagReduction` — general form, given a factorization
  `g = γ_L · diag(1, k) · γ_R` with `γ_L, γ_R ∈ H`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped Pointwise MatrixGroups

/-- For `γ ∈ Γ₀(kN) ⊆ Γ₀(N)`, the nebentypus value at level `N` is the
image of the level-`kN` nebentypus value under `ZMod.unitsMap`. -/
lemma Gamma0MapUnits_unitsMap_of_Gamma0_mul (N k : ℕ) [NeZero N] [NeZero (k * N)]
    (γ : SL(2, ℤ)) (hγ_kN : γ ∈ Gamma0 (k * N))
    (hγ_N : γ ∈ Gamma0 N) :
    Gamma0MapUnits (⟨γ, hγ_N⟩ : ↥(Gamma0 N)) =
      ZMod.unitsMap (Nat.dvd_mul_left N k)
        (Gamma0MapUnits (⟨γ, hγ_kN⟩ : ↥(Gamma0 (k * N)))) := by
  apply Units.ext
  rw [Gamma0MapUnits_val, ZMod.unitsMap_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast (Nat.dvd_mul_left N k) (γ.val 1 1)).symm

/-- **Diamond lift across a level inclusion.**  For any nebentypus value
`d : (ZMod N)ˣ` at level `N`, there exists `β ∈ Γ₀(k · N)` whose `Γ₀(N)`-nebentypus
value is `d` (equivalently, its `Γ₀(k · N)`-value projects onto `d` along `ZMod.unitsMap`). -/
theorem exists_Gamma0_mul_lift_unitsMap
    (N k : ℕ) [NeZero N] [NeZero (k * N)] (d : (ZMod N)ˣ) :
    ∃ β : ↥(Gamma0 (k * N)),
      ZMod.unitsMap (Nat.dvd_mul_left N k) (Gamma0MapUnits β) = d := by
  obtain ⟨d', hd'⟩ :=
    ZMod.unitsMap_surjective (m := k * N) (n := N) (Nat.dvd_mul_left N k) d
  obtain ⟨β, hβ⟩ := Gamma0MapUnits_surjective (N := k * N) d'
  exact ⟨β, by rw [hβ, hd']⟩

/-- **Diamond lift across a level inclusion, `N ∣ M` form.**  Variant of
`exists_Gamma0_mul_lift_unitsMap` stated in terms of a divisibility `N ∣ M`
rather than an explicit product `k · N`. -/
theorem exists_Gamma0_lift_of_dvd
    {M N : ℕ} [NeZero M] (h : N ∣ M) (d : (ZMod N)ˣ) :
    ∃ β : ↥(Gamma0 M),
      ZMod.unitsMap h (Gamma0MapUnits β) = d := by
  obtain ⟨d', hd'⟩ := ZMod.unitsMap_surjective (m := M) (n := N) h d
  obtain ⟨β, hβ⟩ := Gamma0MapUnits_surjective (N := M) d'
  exact ⟨β, by rw [hβ, hd']⟩

/-- **Gamma0MapUnits is surjective on the diagonal stabilizer**.

For `g = diag(1, k) ∈ Δ₀(N)` with `gcd(k, N) = 1`, and any `d ∈ (ZMod N)ˣ`,
there exists `γ_SL ∈ Γ₀(N)` whose GL₂(ℚ)-image lies in the stabilizer
`(ConjAct g • H).subgroupOf H` and has `Gamma0MapUnits γ_SL = d`. -/
theorem Gamma0MapUnits_surjOn_stab_diag
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k) (d : (ZMod N)ˣ) :
    ∃ (γ : (Gamma0_pair N).H),
      γ ∈ (ConjAct.toConjAct
          (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H ∧
      ∃ (γ_SL : ↥(Gamma0 N)),
        (mapGL ℚ (γ_SL : SL(2, ℤ)) : GL (Fin 2) ℚ) = γ ∧
        Gamma0MapUnits γ_SL = d := by
  haveI : NeZero (k * N) := ⟨by
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    exact Nat.mul_pos hk hN_pos |>.ne'⟩
  obtain ⟨d', hd'_map⟩ :=
    ZMod.unitsMap_surjective (m := k * N) (n := N) (Nat.dvd_mul_left N k) d
  obtain ⟨σ_kN, hσ_kN_map⟩ :=
    Gamma0MapUnits_surjective (N := k * N) d'
  set σ : SL(2, ℤ) := (σ_kN : SL(2, ℤ))
  have hσ_mem_kN : σ ∈ Gamma0 (k * N) := σ_kN.property
  have hσ_mem_N : σ ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ_mem_kN ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_left N k)) hσ_mem_kN
  set σ_N : ↥(Gamma0 N) := ⟨σ, hσ_mem_N⟩
  set γ_gl : GL (Fin 2) ℚ := mapGL ℚ σ
  have hγ_H : γ_gl ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨σ, hσ_mem_N, rfl⟩
  refine ⟨⟨γ_gl, hγ_H⟩, ?_, σ_N, rfl, ?_⟩
  · rw [stab_diag_eq_Gamma0 N k hk, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨σ, hσ_mem_kN, rfl⟩
  · have hbridge := Gamma0MapUnits_unitsMap_of_Gamma0_mul N k σ hσ_mem_kN
    show Gamma0MapUnits σ_N = d
    rw [hbridge, hσ_kN_map, hd'_map]

private lemma Gamma0MapUnits_conj_eq {N : ℕ} (a b : ↥(Gamma0 N)) :
    Gamma0MapUnits (a⁻¹ * b * a) = Gamma0MapUnits b := by
  rw [map_mul, map_mul, map_inv]
  exact inv_mul_cancel_comm _ _

private lemma mem_H_conj_of_source_stab {N : ℕ} [NeZero N]
    (g_target g_source γ_src_gl : GL (Fin 2) ℚ) (γ_L γ_R : (Gamma0_pair N).H)
    (h_eq : g_source = (γ_L : GL (Fin 2) ℚ) * g_target * (γ_R : GL (Fin 2) ℚ))
    (h_src : g_source⁻¹ * γ_src_gl * g_source ∈ (Gamma0_pair N).H) :
    g_target⁻¹ * ((γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)) * g_target
      ∈ (Gamma0_pair N).H := by
  have h_conj_eq :
      g_target⁻¹ * ((γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)) * g_target =
        (γ_R : GL (Fin 2) ℚ) * (g_source⁻¹ * γ_src_gl * g_source) *
          (γ_R : GL (Fin 2) ℚ)⁻¹ := by
    subst h_eq; group
  rw [h_conj_eq]
  exact (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.mul_mem γ_R.property h_src)
    ((Gamma0_pair N).H.inv_mem γ_R.property)

/-- **Stabilizer-surjectivity transports across the `Γ₀(N)`-double coset action**.

If `g_source` is obtained from `g_target` by `Γ₀(N)`-conjugation
(`g_source = γ_L · g_target · γ_R` with `γ_L, γ_R ∈ (Gamma0_pair N).H`), and the
stabilizer-surjectivity of `Gamma0MapUnits` holds at `g_source`, then it also holds at
`g_target`. -/
theorem Gamma0MapUnits_surjOn_stab_transport
    {N : ℕ} [NeZero N] (g_target : GL (Fin 2) ℚ) (g_source : GL (Fin 2) ℚ)
    (γ_L γ_R : (Gamma0_pair N).H)
    (h_eq : g_source = (γ_L : GL (Fin 2) ℚ) * g_target * (γ_R : GL (Fin 2) ℚ))
    (h_source : ∀ (d : (ZMod N)ˣ),
      ∃ (γ : (Gamma0_pair N).H),
        γ ∈ (ConjAct.toConjAct g_source •
          (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H ∧
        ∃ (γ_SL : ↥(Gamma0 N)),
          (mapGL ℚ (γ_SL : SL(2, ℤ)) : GL (Fin 2) ℚ) = γ ∧
          Gamma0MapUnits γ_SL = d)
    (d : (ZMod N)ˣ) :
    ∃ (γ : (Gamma0_pair N).H),
      γ ∈ (ConjAct.toConjAct g_target •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H ∧
      ∃ (γ_SL : ↥(Gamma0 N)),
        (mapGL ℚ (γ_SL : SL(2, ℤ)) : GL (Fin 2) ℚ) = γ ∧
        Gamma0MapUnits γ_SL = d := by
  obtain ⟨γ_src, hγ_src_stab, γ_SL_src, hγ_SL_src_eq, hγ_SL_src_map⟩ := h_source d
  obtain ⟨γ_src_gl, hγ_src_gl_H⟩ := γ_src
  set γ_tgt_gl : GL (Fin 2) ℚ :=
    (γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)
  have hγ_tgt_H : γ_tgt_gl ∈ (Gamma0_pair N).H :=
    (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.mul_mem
      ((Gamma0_pair N).H.inv_mem γ_L.property) hγ_src_gl_H) γ_L.property
  have hγ_tgt_stab :
      (⟨γ_tgt_gl, hγ_tgt_H⟩ : (Gamma0_pair N).H) ∈
      (ConjAct.toConjAct g_target •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H := by
    simp only [Subgroup.mem_subgroupOf,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hγ_src_stab ⊢
    exact mem_H_conj_of_source_stab g_target g_source γ_src_gl γ_L γ_R h_eq hγ_src_stab
  obtain ⟨γ_L_SL, hγ_L_SL_mem, hγ_L_SL_eq⟩ := Subgroup.mem_map.mp γ_L.property
  set γ_SL_tgt : SL(2, ℤ) := γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL
  have hγ_SL_tgt_mem : γ_SL_tgt ∈ Gamma0 N :=
    (Gamma0 N).mul_mem ((Gamma0 N).mul_mem
      ((Gamma0 N).inv_mem hγ_L_SL_mem) γ_SL_src.property) hγ_L_SL_mem
  have hγ_SL_tgt_eq : (mapGL ℚ γ_SL_tgt : GL (Fin 2) ℚ) = γ_tgt_gl := by
    show (mapGL ℚ (γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL) : GL (Fin 2) ℚ) =
      (γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)
    simp only [map_mul, map_inv]
    rw [hγ_L_SL_eq, hγ_SL_src_eq]
  have hγ_SL_tgt_map : Gamma0MapUnits ⟨γ_SL_tgt, hγ_SL_tgt_mem⟩ = d := by
    have h_prod_eq : (⟨γ_SL_tgt, hγ_SL_tgt_mem⟩ : ↥(Gamma0 N)) =
        (⟨γ_L_SL, hγ_L_SL_mem⟩ : ↥(Gamma0 N))⁻¹ * γ_SL_src *
          ⟨γ_L_SL, hγ_L_SL_mem⟩ := by
      apply Subtype.ext; simp [γ_SL_tgt, mul_assoc]
    rw [h_prod_eq, Gamma0MapUnits_conj_eq, hγ_SL_src_map]
  exact ⟨⟨γ_tgt_gl, hγ_tgt_H⟩, hγ_tgt_stab,
    ⟨γ_SL_tgt, hγ_SL_tgt_mem⟩, hγ_SL_tgt_eq, hγ_SL_tgt_map⟩

/-- **Stab-surjectivity from diagonal reduction** (specialized form).

If `g ∈ Δ₀(N)` is `Γ₀(N)`-double-coset-equivalent to `diag(1, k)` for some
positive `k`, then `Gamma0MapUnits` is surjective on `Stab(g)`. -/
theorem Gamma0MapUnits_surjOn_stab_of_diagReduction
    {N : ℕ} [NeZero N] (g : GL (Fin 2) ℚ) (k : ℕ) (hk : 0 < k)
    (γ_L γ_R : (Gamma0_pair N).H)
    (h_eq : g = (γ_L : GL (Fin 2) ℚ) *
      (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) *
      (γ_R : GL (Fin 2) ℚ))
    (d : (ZMod N)ˣ) :
    ∃ (γ : (Gamma0_pair N).H),
      γ ∈ (ConjAct.toConjAct g •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H ∧
      ∃ (γ_SL : ↥(Gamma0 N)),
        (mapGL ℚ (γ_SL : SL(2, ℤ)) : GL (Fin 2) ℚ) = γ ∧
        Gamma0MapUnits γ_SL = d := by
  apply Gamma0MapUnits_surjOn_stab_transport
    (g_target := g)
    (g_source := (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
    ⟨(γ_L : GL (Fin 2) ℚ)⁻¹, (Gamma0_pair N).H.inv_mem γ_L.property⟩
    ⟨(γ_R : GL (Fin 2) ℚ)⁻¹, (Gamma0_pair N).H.inv_mem γ_R.property⟩
  · show (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) =
      (γ_L : GL (Fin 2) ℚ)⁻¹ * g * (γ_R : GL (Fin 2) ℚ)⁻¹
    rw [h_eq]; group
  · exact fun d' ↦ Gamma0MapUnits_surjOn_stab_diag N k hk d'

end HeckeRing.GL2.Prop334
