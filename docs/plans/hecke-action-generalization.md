# Refactoring Spec: Generalized Hecke Action for Arbitrary Hecke Pairs

## Motivation

Currently `heckeSlash`, `heckeSlashExt`, and `heckeSlash_comp` in `GL2/HeckeAction.lean` 
and `GL2/HeckeModularForm.lean` are hardcoded to `GL_pair 2` (the level-1 Hecke pair 
SL₂(ℤ) ⊂ GL₂⁺(ℚ)). This means:

- The composition theorem `heckeSlash_comp` requires SL₂(ℤ)-invariance of f
- We can't use it for Γ₁(N)-forms (which are only Γ₁(N)-invariant)
- Commutativity of T_p operators at level N was proved by ~500 lines of direct 
  matrix computation instead of the one-line argument "the Hecke algebra is 
  commutative and the action is a ring homomorphism"

The fix: generalize from `GL_pair 2` to any `P : HeckePair (GL (Fin 2) ℚ)`.

## What Exists (Already Generic)

The abstract Hecke ring machinery is ALREADY parameterized by `P`:
- `decompQuot P g` — left coset decomposition of HgH (AbstractHeckeRing/Basic.lean:368)
- `mulMap P g₁ g₂` — maps pairs of coset reps to double cosets (Multiplication.lean:166)
- `heckeMultiplicity P g₁ g₂ d` — fiber counting (Multiplication.lean:174)
- `heckeMultiplicity_uniform` — uniform multiplicity (Associativity.lean)
- `GL_transposeEquiv n` — transpose on GL_n(ℚ) for any n (TransposeAntiInvolution.lean:30)
- `instCommRing_Gamma0 N` — CommRing for level-N Hecke algebra (CongruenceHecke.lean:2997)

## What Needs Generalization

### File: `GL2/HeckeAction.lean`

**`tRep`** (line 115-118): Currently:
```lean
noncomputable abbrev tRep (D : HeckeCoset (GL_pair 2))
    (i : decompQuot (GL_pair 2) (HeckeCoset.rep D)) : GL (Fin 2) ℚ :=
  (GL_transposeEquiv 2 ((i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ))).unop
```
Generalize to:
```lean
noncomputable abbrev tRep_gen (P : HeckePair (GL (Fin 2) ℚ))
    (D : HeckeCoset P) (i : decompQuot P (HeckeCoset.rep D)) : GL (Fin 2) ℚ :=
  (GL_transposeEquiv 2 ((i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ))).unop
```
Note: `GL_transposeEquiv 2` works for ANY HeckePair inside GL₂(ℚ), not just GL_pair 2.

**Helper lemmas** that need `GL_pair 2` → `P` generalization:
| Lemma | Line | Change needed |
|-------|------|---------------|
| `delta_det_pos_real` | ~68 | Add hypothesis `∀ g ∈ P.Δ, 0 < det(glMap g)` |
| `SLnZ_det_one_real` | ~72 | Add hypothesis `∀ h ∈ P.H, det(glMap h) = 1` (or just > 0) |
| `cosetRep_delta_det_pos` | ~78 | Same det-positivity hypothesis |
| `sigma_eq_id_for_pos_det` | ~85 | Same |
| `slash_H_eq` | ~95 | Replace `∀ γ ∈ 𝒮ℒ` with `∀ γ ∈ image(P.H)` |
| `leftMulQuot` / `leftMulEquiv` | ~130-155 | Replace `GL_pair 2` with `P` |
| `slash_left_H_transpose_mul` | ~170 | Replace `𝒮ℒ` with `P.H` image |
| `tRep_mul_eq_transpose` | ~190 | Replace `GL_pair 2` with `P` |

The key observation: ALL these lemmas work for any P where:
1. Elements of P.Δ have positive real determinant under glMap
2. Elements of P.H map to the relevant subgroup under mapGL ℝ

Both `GL_pair 2`, `Gamma0_pair N`, and `Gamma1_pair N` satisfy these conditions.

### File: `GL2/HeckeModularForm.lean`

**`heckeSlash`** (line 127-128): Replace `HeckeCoset (GL_pair 2)` with `HeckeCoset P`:
```lean
noncomputable def heckeSlash_gen (P : HeckePair (GL (Fin 2) ℚ)) (k : ℤ) 
    (D : HeckeCoset P) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot P (HeckeCoset.rep D), f ∣[k] tRep_gen P D i
```

**`heckeSlashExt`** (line 281-282): Replace `HeckeAlgebra 2` with `𝕋 P ℤ`:
```lean
noncomputable def heckeSlashExt_gen (P : HeckePair (GL (Fin 2) ℚ)) (k : ℤ) 
    (T : 𝕋 P ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c => c • heckeSlash_gen P k D f)
```

**`heckeSlash_comp`** (line 293-337): THE KEY THEOREM. Currently:
```lean
private theorem heckeSlash_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) : 
    heckeSlash k D₁ (heckeSlash k D₂ f) =
    heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) f
```
Generalize to:
```lean
theorem heckeSlash_gen_comp (P : HeckePair (GL (Fin 2) ℚ)) [hP : HeckePairAction P]
    (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ P.H, f ∣[k] (glMap γ) = f) :    -- ← generalized invariance
    heckeSlash_gen P k D₁ (heckeSlash_gen P k D₂ f) =
    heckeSlashExt_gen P k (T_single P ℤ D₂ 1 * T_single P ℤ D₁ 1) f
```
The proof is the SAME structure — it uses `mulMap`, `heckeMultiplicity_uniform`, 
and `heckeSlash_fiber_sum`, all of which only need the `P` parameter. The only 
GL_pair-specific ingredients are the det-positivity and H-invariance lemmas, 
which generalize as described above.

**`heckeSlash_fiber_sum`** (line 195-272): Also needs `GL_pair 2` → `P`. 
The proof uses `heckeMultiplicity_uniform P ...` (already generic) plus the 
`slash_left_H_transpose_mul` helper (needs generalization as above).

## The Payoff: Commutativity as One Line

Once the generalization is done, commutativity of level-N operators becomes:

```lean
theorem heckeSlash_gen_comm (P : HeckePair (GL (Fin 2) ℚ)) 
    [hP : HeckePairAction P] [CommRing (𝕋 P ℤ)]
    (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ) (hf : ∀ γ ∈ P.H, f ∣[k] (glMap γ) = f) :
    heckeSlash_gen P k D₁ (heckeSlash_gen P k D₂ f) = 
    heckeSlash_gen P k D₂ (heckeSlash_gen P k D₁ f) := by
  rw [heckeSlash_gen_comp, heckeSlash_gen_comp]
  congr 1
  exact mul_comm _ _
```

And `heckeT_p_all_comm_distinct` follows from showing `heckeT_p_all p = heckeSlash_gen (Gamma1_pair N) k D_p`.

## The Ring Homomorphism (the TODO at line 354)

Once `heckeSlash_gen_comp` is proved, package the action as:
```lean
noncomputable def heckeActionHom (P : HeckePair (GL (Fin 2) ℚ)) [HeckePairAction P]
    (k : ℤ) : (𝕋 P ℤ)ᵐᵒᵖ →+* Module.End ℂ (ModularForm (P.H.map (mapGL ℝ)) k) := ...
```
Since `𝕋 P ℤ` is commutative (when `CommRing` instance exists), `ᵐᵒᵖ ≃ id`, so this 
is also a regular ring homomorphism.

## Typeclass for Hecke Pair Analytic Data

The generalization needs a way to express "P.H maps to a subgroup acting on ℍ" and 
"P.Δ has positive determinant". Define:

```lean
class HeckePairAction (P : HeckePair (GL (Fin 2) ℚ)) where
  det_pos : ∀ g : P.Δ, 0 < (glMap (g : GL _ ℚ)).1.det
  -- Ensures slash action σ is trivial (σ = id for positive det)
```

This is satisfied by `GL_pair 2`, `Gamma0_pair N`, and `Gamma1_pair N` since all 
their Δ-submonoids consist of positive-determinant matrices.

The Γ-invariance `∀ γ ∈ P.H, f ∣[k] (glMap γ) = f` is NOT part of the typeclass — 
it's a hypothesis on f (it says f is a modular form for the group P.H).

## Implementation Plan

### Step 1: Create `GL2/HeckeActionGeneral.lean` (~200 lines)
- Define `tRep_gen`, `heckeSlash_gen`, `heckeSlashExt_gen`
- Define `HeckePairAction` typeclass
- Port `slash_H_eq`, `leftMulEquiv`, `slash_left_H_transpose_mul` generically
- These are mechanical: replace `GL_pair 2` with `P`, `𝒮ℒ` with `P.H.map (mapGL ℝ)`, 
  add `[HeckePairAction P]`

### Step 2: Port `heckeSlash_fiber_sum` (~100 lines)
- Same proof structure as existing, with `P` parameter
- Uses `heckeMultiplicity_uniform P` (already generic)

### Step 3: Port `heckeSlash_comp` (~50 lines)
- Same proof, using generalized helpers from Steps 1-2

### Step 4: Derive commutativity corollary (~10 lines)
- `heckeSlash_gen_comm` from `heckeSlash_gen_comp` + `mul_comm`

### Step 5: Connect to concrete operators (~50 lines)
- Show `heckeT_p_all p = heckeSlash_gen (Gamma1_pair N) k D_p` 
  where D_p = double coset of diag(1,p) in Gamma1_pair N
- This requires matching the coset representatives (the [[1,b;0,p]] + diamond twist)

### Step 6: Package ring homomorphism (~30 lines)  
- Define `heckeActionHom` as the TODO requests
- Show it's a well-defined ring homomorphism

### Step 7: Refactor existing proofs (optional)
- Replace the 500-line direct commutativity proof in HeckeT_n.lean with the 
  one-line proof via the ring homomorphism
- Replace `heckeOperator_comp` with `heckeSlash_gen_comp` instantiated at GL_pair 2

## Estimated effort: ~400-500 lines of new code

Most is mechanical porting (replacing `GL_pair 2` with `P`). The key new content is:
- The `HeckePairAction` typeclass (~10 lines)  
- Step 5: matching coset representatives (~50 lines, the "bridge" computation)
- Step 6: packaging the ring homomorphism (~30 lines)

## Files to read before starting
1. `GL2/HeckeAction.lean` — current implementation (380 lines)
2. `GL2/HeckeModularForm.lean` — heckeSlash_comp (360 lines)
3. `AbstractHeckeRing/Multiplication.lean` — generic mulMap/heckeMultiplicity
4. `GLn/TransposeAntiInvolution.lean` — GL_transposeEquiv (generic)
5. `GL2/Gamma1Pair.lean` — Gamma1_pair definition

## Success criteria
- `heckeSlash_gen_comp` proved for arbitrary `P : HeckePair (GL (Fin 2) ℚ)` with `[HeckePairAction P]`
- `heckeSlash_gen_comm` proved using `[CommRing (𝕋 P ℤ)]` + `heckeSlash_gen_comp`
- `heckeT_p_all k p = heckeSlash_gen (Gamma1_pair N) k D_p` proved
- `heckeT_p_all_comm_distinct` reproved in ≤5 lines using the above
- All existing downstream theorems still compile
