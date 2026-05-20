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

  `(ConjAct g • (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H`

maps surjectively onto `(ZMod N)ˣ` under `Gamma0MapUnits`.

This is a key step for the preservation of `modFormCharSpace k χ` under
`heckeSlash_gen` (Prop 3.34-E).

## Main results

* `Gamma0MapUnits_surjOn_stab_diag` — The surjectivity statement for the
  diagonal case `g = diag(1, k)`. This is the complete, sorry-free proof
  for diagonal elements and the case directly used by `heckeT_p` for
  `p` coprime to `N` (where `g = diag(1, p)`).
* `Gamma0MapUnits_surjOn_stab_transport` — Transports stabilizer
  surjectivity across the `Γ₀(N)`-double coset action, using the
  abelianness of `(ZMod N)ˣ` to conjugate away `Γ₀(N)`-factors.
* `Gamma0MapUnits_surjOn_stab_of_diagReduction` — General-form theorem:
  given a factorization `g = γ_L · diag(1, k) · γ_R` with `γ_L, γ_R ∈ H`,
  stabilizer surjectivity holds at `g`. Applications supply the
  factorization via `shimura_prop_3_33_gen` (CongruenceHecke.lean).

## Strategy

The diagonal case is handled directly via:
1. `stab_diag_eq_Gamma0` (CongruenceHecke.lean) identifies the stabilizer
   inside `H = Γ₀(N).map(mapGL)` as `Γ₀(kN).map(mapGL).subgroupOf H`.
2. `Gamma0MapUnits_surjective` at level `kN` produces a lift of any
   `(ZMod (kN))ˣ`-unit to `Γ₀(kN)`.
3. `ZMod.unitsMap_surjective` lifts any `d ∈ (ZMod N)ˣ` through the
   projection `(ZMod (kN))ˣ → (ZMod N)ˣ` (well-defined since `N ∣ kN`).
4. The compatibility `Gamma0MapUnits (γ ∈ Γ₀(kN)) ↦ ZMod.unitsMap`
   pushes the lift forward to `(ZMod N)ˣ`, giving the required
   surjectivity.

The general case reduces to the diagonal one via the transport lemma:
for `g = γ_L · diag(1, k) · γ_R`, conjugation by `γ_L⁻¹` maps the
stabilizer of `diag(1, k)` to the stabilizer of `g`, and
`Gamma0MapUnits` is invariant under this conjugation by abelianness
of `(ZMod N)ˣ`.

To obtain the `γ_L, γ_R` factorization from a general `g ∈ Δ₀(N)`
with coprime det, the canonical route is `shimura_prop_3_33_gen`
combined with primitivity-clearing via
`Gamma0_two_sided_coprime_rep_prim`. This reduction is NOT performed
in this file (it requires resolving an existing `sorry` in
`CongruenceHecke.lean` for the non-primitive content-reduction step).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped Pointwise MatrixGroups

/-! ### Compatibility of `Gamma0MapUnits` with `ZMod.unitsMap` -/

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
`d : (ZMod N)ˣ` at level `N`, there exists `β ∈ Γ₀(k · N)` whose
`Γ₀(N)`-nebentypus value is `d` (equivalently, its `Γ₀(k · N)`-value
projects onto `d` along `ZMod.unitsMap`).

This is the reusable building block for descending diamond operators
from a deeper level `k · N` back to `N`: it supplies a single
representative `β` that is simultaneously in `Γ₀(k · N)` (so it
normalises `Γ₁(k · N)`) and represents the class `d` at level `N`.
The argument is a direct two-step lift via `ZMod.unitsMap_surjective`
and `Gamma0MapUnits_surjective` combined through the compatibility
lemma `Gamma0MapUnits_unitsMap_of_Gamma0_mul`. -/
theorem exists_Gamma0_mul_lift_unitsMap
    (N k : ℕ) [NeZero N] [NeZero (k * N)] (d : (ZMod N)ˣ) :
    ∃ β : ↥(Gamma0 (k * N)),
      ZMod.unitsMap (Nat.dvd_mul_left N k) (Gamma0MapUnits β) = d := by
  -- Lift `d` to `(ZMod (k · N))ˣ` along `ZMod.unitsMap`.
  obtain ⟨d', hd'⟩ :=
    ZMod.unitsMap_surjective (m := k * N) (n := N) (Nat.dvd_mul_left N k) d
  -- Realise `d'` as the `Γ₀(k · N)`-nebentypus of some `β`.
  obtain ⟨β, hβ⟩ := Gamma0MapUnits_surjective (N := k * N) d'
  exact ⟨β, by rw [hβ, hd']⟩

/-- **Diamond lift across a level inclusion, `N ∣ M` form.**  Variant of
`exists_Gamma0_mul_lift_unitsMap` stated directly in terms of a
divisibility `N ∣ M` (rather than an explicit product `k · N`).  The
proof is the same two-step lift via `ZMod.unitsMap_surjective` and
`Gamma0MapUnits_surjective`. -/
theorem exists_Gamma0_lift_of_dvd
    {M N : ℕ} [NeZero M] (h : N ∣ M) (d : (ZMod N)ˣ) :
    ∃ β : ↥(Gamma0 M),
      ZMod.unitsMap h (Gamma0MapUnits β) = d := by
  obtain ⟨d', hd'⟩ := ZMod.unitsMap_surjective (m := M) (n := N) h d
  obtain ⟨β, hβ⟩ := Gamma0MapUnits_surjective (N := M) d'
  exact ⟨β, by rw [hβ, hd']⟩

/-! ### Diagonal-case surjectivity -/

/-- **Gamma0MapUnits is surjective on the diagonal stabilizer**.

For `g = diag(1, k) ∈ Δ₀(N)` with `gcd(k, N) = 1`, and any `d ∈ (ZMod N)ˣ`,
there exists `γ_SL ∈ Γ₀(N)` whose GL₂(ℚ)-image lies in the stabilizer
`(ConjAct g • H).subgroupOf H` AND has `Gamma0MapUnits γ_SL = d`.

The proof takes a `Γ₀(kN)`-preimage of the lift of `d` to `(ZMod (kN))ˣ`
and shows that (a) it lies in the stabilizer via `stab_diag_eq_Gamma0`
and (b) its `Γ₀(N)`-nebentypus equals `d` via `ZMod.unitsMap_surjective`
and the `Gamma0MapUnits`/`ZMod.unitsMap` compatibility. -/
theorem Gamma0MapUnits_surjOn_stab_diag
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k) (d : (ZMod N)ˣ) :
    ∃ (γ : (Gamma0_pair N).H),
      γ ∈ (ConjAct.toConjAct
          (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H ∧
      ∃ (γ_SL : ↥(Gamma0 N)),
        (mapGL ℚ (γ_SL : SL(2, ℤ)) : GL (Fin 2) ℚ) = γ ∧
        Gamma0MapUnits γ_SL = d := by
  -- Set up the level kN
  haveI : NeZero (k * N) := ⟨by
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    exact Nat.mul_pos hk hN_pos |>.ne'⟩
  -- Step 1: lift d ∈ (ZMod N)ˣ to d' ∈ (ZMod (kN))ˣ via unitsMap surjectivity.
  obtain ⟨d', hd'_map⟩ :=
    ZMod.unitsMap_surjective (m := k * N) (n := N) (Nat.dvd_mul_left N k) d
  -- Step 2: find σ ∈ Γ₀(kN) with Gamma0MapUnits σ = d' (via Gamma0MapUnits_surjective).
  obtain ⟨σ_kN, hσ_kN_map⟩ :=
    Gamma0MapUnits_surjective (N := k * N) d'
  -- Step 3: Project σ_kN into Γ₀(N). Call this σ_N.
  set σ : SL(2, ℤ) := (σ_kN : SL(2, ℤ))
  have hσ_mem_kN : σ ∈ Gamma0 (k * N) := σ_kN.property
  have hσ_mem_N : σ ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ_mem_kN ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_left N k)) hσ_mem_kN
  set σ_N : ↥(Gamma0 N) := ⟨σ, hσ_mem_N⟩
  -- Step 4: γ := mapGL ℚ σ ∈ H, and it's in the stabilizer via stab_diag_eq_Gamma0.
  set γ_gl : GL (Fin 2) ℚ := mapGL ℚ σ
  have hγ_H : γ_gl ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨σ, hσ_mem_N, rfl⟩
  refine ⟨⟨γ_gl, hγ_H⟩, ?_, σ_N, rfl, ?_⟩
  · -- Stabilizer membership via stab_diag_eq_Gamma0.
    rw [stab_diag_eq_Gamma0 N k hk]
    rw [Subgroup.mem_subgroupOf]
    show γ_gl ∈ (Gamma0 (k * N)).map (mapGL ℚ)
    exact Subgroup.mem_map.mpr ⟨σ, hσ_mem_kN, rfl⟩
  · -- Gamma0MapUnits σ_N = d.
    -- Bridge: σ_N at level N has the same (1,1) entry as σ_kN at level kN,
    -- so Gamma0MapUnits σ_N = unitsMap (Gamma0MapUnits σ_kN) = unitsMap d' = d.
    have hbridge := Gamma0MapUnits_unitsMap_of_Gamma0_mul N k σ hσ_mem_kN
    -- hbridge : Gamma0MapUnits σ_N = unitsMap (Gamma0MapUnits σ_kN)
    -- Substitute Gamma0MapUnits σ_kN = d'
    -- Replace Gamma0MapUnits (⟨σ, hσ_mem_kN⟩) via σ_kN (they should be equal).
    have hσ_eq : (⟨σ, hσ_mem_kN⟩ : ↥(Gamma0 (k * N))) = σ_kN := rfl
    rw [hσ_eq] at hbridge
    show Gamma0MapUnits σ_N = d
    rw [hbridge, hσ_kN_map, hd'_map]

/-! ### Double-coset transport of stabilizer surjectivity

If `g' = γ_L · g · γ_R` with `γ_L, γ_R ∈ H` (the `Γ₀(N)`-part of the Hecke pair),
then the stabilizers of `g` and `g'` have the same image under `Gamma0MapUnits`.
This uses (a) `Stab(g') = γ_L · Stab(g) · γ_L⁻¹` and (b) the commutativity of
`(ZMod N)ˣ`, so `Gamma0MapUnits(γ_L · γ · γ_L⁻¹) = Gamma0MapUnits(γ)`. -/

/-- **Stabilizer-surjectivity transports across the `Γ₀(N)`-double coset action**.

If `g_source` is obtained from `g_target` by `Γ₀(N)`-conjugation (`g_source = γ_L · g_target · γ_R`
with `γ_L, γ_R ∈ (Gamma0_pair N).H`), and the stabilizer-surjectivity of
`Gamma0MapUnits` holds at `g_source`, then it also holds at `g_target`. -/
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
  -- Apply the source surjectivity
  obtain ⟨γ_src, hγ_src_stab, γ_SL_src, hγ_SL_src_eq, hγ_SL_src_map⟩ := h_source d
  -- Conjugate by γ_L⁻¹ to land in Stab(g_target)
  -- New γ = γ_L⁻¹ · γ_src · γ_L
  -- Unpack γ_src as subgroup element
  obtain ⟨γ_src_gl, hγ_src_gl_H⟩ := γ_src
  set γ_tgt_gl : GL (Fin 2) ℚ :=
    (γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)
  -- γ_tgt_gl ∈ H (closure under conjugation in H)
  have hγ_tgt_H : γ_tgt_gl ∈ (Gamma0_pair N).H := by
    have hγ_L_inv : ((γ_L : GL (Fin 2) ℚ)⁻¹) ∈ (Gamma0_pair N).H :=
      (Gamma0_pair N).H.inv_mem γ_L.property
    exact (Gamma0_pair N).H.mul_mem
      ((Gamma0_pair N).H.mul_mem hγ_L_inv hγ_src_gl_H) γ_L.property
  -- γ_tgt_gl ∈ Stab(g_target)
  have hγ_tgt_stab :
      (⟨γ_tgt_gl, hγ_tgt_H⟩ : (Gamma0_pair N).H) ∈
      (ConjAct.toConjAct g_target •
        (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H := by
    -- hγ_src_stab : γ_src ∈ (ConjAct g_source • H).subgroupOf H
    -- i.e., g_source⁻¹ · γ_src · g_source ∈ H.
    simp only [Subgroup.mem_subgroupOf,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hγ_src_stab ⊢
    -- Goal: g_target⁻¹ · γ_tgt_gl · g_target ∈ H.
    -- Compute: g_target⁻¹ · γ_tgt_gl · g_target =
    --         (γ_R) · (g_source⁻¹ · γ_src_gl · g_source) · (γ_R)⁻¹
    -- via group laws and h_eq.
    have h_conj_eq :
        g_target⁻¹ * γ_tgt_gl * g_target =
          (γ_R : GL (Fin 2) ℚ) *
            (g_source⁻¹ * γ_src_gl * g_source) *
            (γ_R : GL (Fin 2) ℚ)⁻¹ := by
      subst h_eq
      show g_target⁻¹ * ((γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl *
        (γ_L : GL (Fin 2) ℚ)) * g_target = _
      group
    rw [h_conj_eq]
    -- R · (stuff ∈ H) · R⁻¹ ∈ H.
    exact (Gamma0_pair N).H.mul_mem
      ((Gamma0_pair N).H.mul_mem γ_R.property hγ_src_stab)
      ((Gamma0_pair N).H.inv_mem γ_R.property)
  -- Build γ_SL_tgt
  -- γ_L = mapGL γ_L_SL for some γ_L_SL ∈ Γ₀(N)
  obtain ⟨γ_L_SL, hγ_L_SL_mem, hγ_L_SL_eq⟩ := Subgroup.mem_map.mp γ_L.property
  -- γ_tgt_gl = mapGL (γ_L_SL⁻¹ * γ_SL_src * γ_L_SL)
  set γ_SL_tgt : SL(2, ℤ) := γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL
  have hγ_SL_tgt_mem : γ_SL_tgt ∈ Gamma0 N := by
    have h1 : γ_L_SL⁻¹ ∈ Gamma0 N := (Gamma0 N).inv_mem hγ_L_SL_mem
    exact (Gamma0 N).mul_mem ((Gamma0 N).mul_mem h1 γ_SL_src.property) hγ_L_SL_mem
  -- The mapGL relation
  have hγ_SL_tgt_eq : (mapGL ℚ γ_SL_tgt : GL (Fin 2) ℚ) = γ_tgt_gl := by
    show (mapGL ℚ (γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL) : GL (Fin 2) ℚ) =
      (γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)
    simp only [map_mul, map_inv]
    rw [hγ_L_SL_eq, hγ_SL_src_eq]
  -- Gamma0MapUnits computation: conjugation by γ_L_SL acts trivially
  -- since (ZMod N)ˣ is abelian.
  have hγ_SL_tgt_map : Gamma0MapUnits ⟨γ_SL_tgt, hγ_SL_tgt_mem⟩ = d := by
    have hunits_comm : Gamma0MapUnits ⟨γ_SL_tgt, hγ_SL_tgt_mem⟩ =
        Gamma0MapUnits γ_SL_src := by
      show Gamma0MapUnits (⟨γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL,
        hγ_SL_tgt_mem⟩ : ↥(Gamma0 N)) = Gamma0MapUnits γ_SL_src
      set γ_L_sub : ↥(Gamma0 N) := ⟨γ_L_SL, hγ_L_SL_mem⟩
      have h_prod_eq : (⟨γ_L_SL⁻¹ * (γ_SL_src : SL(2, ℤ)) * γ_L_SL,
          hγ_SL_tgt_mem⟩ : ↥(Gamma0 N)) =
          γ_L_sub⁻¹ * γ_SL_src * γ_L_sub := by
        apply Subtype.ext; simp [γ_L_sub, mul_assoc]
      rw [h_prod_eq, map_mul, map_mul, map_inv]
      set u_L := Gamma0MapUnits γ_L_sub
      set u_src := Gamma0MapUnits γ_SL_src
      show u_L⁻¹ * u_src * u_L = u_src
      rw [mul_comm u_L⁻¹ u_src, mul_assoc, inv_mul_cancel, mul_one]
    rw [hunits_comm, hγ_SL_src_map]
  refine ⟨⟨γ_tgt_gl, hγ_tgt_H⟩, hγ_tgt_stab, ⟨γ_SL_tgt, hγ_SL_tgt_mem⟩, hγ_SL_tgt_eq,
    hγ_SL_tgt_map⟩

/-! ### General-case theorem (conditional on diagonal reduction)

The full theorem for arbitrary `g ∈ Δ₀(N)` with coprime determinant reduces to
the diagonal case via `shimura_prop_3_33_gen` (CongruenceHecke.lean) combined
with primitivity-clearing. This reduction step is left as a ticket; the
transport lemma `Gamma0MapUnits_surjOn_stab_transport` above encapsulates
the final move once the reduction is available. -/

/-- **Stab-surjectivity from diagonal reduction** (specialized form).

If `g ∈ Δ₀(N)` is `Γ₀(N)`-double-coset-equivalent to `diag(1, k)` for some
positive `k`, then `Gamma0MapUnits` is surjective on `Stab(g)`.

To apply: use `shimura_prop_3_33_gen` (CongruenceHecke.lean) to obtain the
factorization `g = γ_L · diag(1, m) · γ_R` under the hypothesis
`gcd(A 0 0, m) = 1` (possibly after primitivity-clearing via
`Gamma0_two_sided_coprime_rep_prim`). -/
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
  -- Use transport from `g_source = diag(1,k)` to `g_target = g` with
  -- conjugator `(γ_L', γ_R') = (γ_L⁻¹, γ_R⁻¹)`:
  -- `g_source = γ_L' · g_target · γ_R'` ⟺ `diag = γ_L⁻¹ · g · γ_R⁻¹`.
  apply Gamma0MapUnits_surjOn_stab_transport
    (g_target := g)
    (g_source := (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
    ⟨(γ_L : GL (Fin 2) ℚ)⁻¹, (Gamma0_pair N).H.inv_mem γ_L.property⟩
    ⟨(γ_R : GL (Fin 2) ℚ)⁻¹, (Gamma0_pair N).H.inv_mem γ_R.property⟩
  · -- diag(1,k) = γ_L⁻¹ · g · γ_R⁻¹
    show (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) =
      (γ_L : GL (Fin 2) ℚ)⁻¹ * g * (γ_R : GL (Fin 2) ℚ)⁻¹
    rw [h_eq]; group
  · exact fun d' => Gamma0MapUnits_surjOn_stab_diag N k hk d'

end HeckeRing.GL2.Prop334
