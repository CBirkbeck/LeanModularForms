# HeckeT_p General Orbit API + Cusp Stability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the 2 remaining sorries in `HeckeT_p.lean` by building general reusable API: (1) generalized orbit factorization for Γ₀(N) that unifies the slash-invariance and orbit-sum-comm proofs, and (2) cusp stability under GL₂(ℚ) for finite-index subgroups using mathlib's `IsCusp.of_isFiniteRelIndex`.

**Architecture:** Two independent API pieces: (A) 4 generalized orbit lemmas for σ ∈ Γ₀(N) replacing the existing Γ₁(N)-specific ones, with diamond operator tracking; (B) a `Gamma1_IsFiniteRelIndex` instance bridging `Subgroup.FiniteIndex` to `IsFiniteRelIndex` for the mapped subgroups. Each task is self-contained and testable via `lean_diagnostic_messages`.

**Tech Stack:** Lean 4, Mathlib (IsCusp.of_isFiniteRelIndex, Subgroup.relIndex_map_map_of_injective, Finset.sum_equiv), lean-lsp MCP tools.

---

### Task 1: Fill `Gamma1_isCusp_glMap_smul` sorry (cusp stability)

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean:1049`

The sorry at line 1049 needs: given `IsCusp (glMap A • c) (⊤.map (mapGL ℝ))`, prove `IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ))`.

Mathlib provides `IsCusp.of_isFiniteRelIndex`:
```lean
lemma IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢
```

We need `[(Gamma1 N).map (mapGL ℝ)].IsFiniteRelIndex [(⊤ : Subgroup SL(2,ℤ)).map (mapGL ℝ)]`.

This follows from `Subgroup.relIndex_map_map_of_injective` + existing `Subgroup.FiniteIndex (Gamma1 N)`.

- [ ] **Step 1: Check that `IsCusp.of_isFiniteRelIndex` is importable**

Use `lean_hover_info` on `IsCusp.of_isFiniteRelIndex` after adding it to the file to confirm it resolves. May need `import Mathlib.NumberTheory.ModularForms.Cusps` (check if already imported transitively).

- [ ] **Step 2: Establish the `IsFiniteRelIndex` instance**

Replace the `sorry` at line 1049 with:
```lean
  -- Γ₁(N) has finite relIndex in SL₂(ℤ), so the mapped subgroups do too
  have : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := by
    constructor
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  exact IsCusp.of_isFiniteRelIndex hsmul_SL
```

- [ ] **Step 3: Verify with `lean_diagnostic_messages`**

Run diagnostics on lines 1029-1070. Expected: 0 errors. The `heckeT_p_bdd_at_cusps` proof should now also be sorry-free since it depends on `Gamma1_isCusp_glMap_smul`.

- [ ] **Step 4: Verify sorry count**

Run `grep -c 'sorry' HeckeT_p.lean`. Expected: 1 (only `orbit_sum_comm` remains).

---

### Task 2: Add 4 generalized orbit lemmas for σ ∈ Γ₀(N)

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean` — add new lemmas after the existing Γ₁(N) orbit lemmas (after line ~780)

These generalize the existing 4 orbit lemmas from σ ∈ Γ₁(N) to σ ∈ Γ₀(N). The matrix factorization is IDENTICAL. The only change: the conclusion uses `diamondOpAux` instead of bare `f`, because τ ∈ Γ₀(N) (not Γ₁).

**Key mathematical fact**: In each factorization `β_b · σ = τ · β_{j'}`, the constructed τ satisfies `Gamma0MapUnits(τ) = Gamma0MapUnits(σ)`. This is because τ₁₁ = M₁₁ - M₁₀·j' ≡ M₁₁ (mod N) since N | M₁₀.

So `diamondOpAux k ⟨τ,_⟩ f = diamondOpAux k ⟨σ,_⟩ f` by `diamondOpAux_eq_of_Gamma0Map_eq`.

- [ ] **Step 2a: Add `orbit_upper_gamma0` — generalized upper→upper**

```lean
/-- **Upper → Upper for Γ₀(N)**: when σ ∈ Γ₀(N) and p ∤ A,
    β_b · σ = τ · β_{φ(b)} with τ ∈ Γ₀(N) and Gamma0Map(τ) = Gamma0Map(σ).
    So f|β_b|σ = (⟨σ⟩f)|β_{φ(b)}. -/
private theorem orbit_upper_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix ...) 0 0 + ↑b.val * (σ : Matrix ...) 1 0)) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      glMap (T_p_upper p hp.pos (moebiusFin p hp (↑σ) b).val)
```

Proof structure: Same matrix factorization as `orbit_upper_moebius`. Construct τ_mat = !![A, q; p*M₁₀, M₁₁-M₁₀*j'], show τ ∈ Gamma0(N) (uses N | M₁₀ from hσ), show `Gamma0Map(τ) = Gamma0Map(σ)` (both ≡ M₁₁ mod N since N | M₁₀), then use `diamondOpAux_eq_of_Gamma0Map_eq` to replace `⟨τ⟩` with `⟨σ⟩`.

- [ ] **Step 2b: Add `orbit_upper_div_gamma0` — generalized upper→lower**

```lean
private theorem orbit_upper_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) ...
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : (p : ℤ) ∣ ...) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos)
```

Same matrix factorization as `orbit_rep_upper_div`. τ has Gamma0Map = p · M₁₁ ≡ p · Gamma0Map(σ). The diamond operator gives `⟨p⟩(⟨σ⟩f)`.

- [ ] **Step 2c: Add `orbit_lower_gamma0` — generalized lower→upper**

```lean
private theorem orbit_lower_gamma0 [NeZero N] (k : ℤ) (p : ℕ) ...
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hσ10 : ¬(p : ℤ) ∣ M 1 0)
    (b₀ : Fin p) (hb₀ : (p : ℤ) ∣ ...) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      glMap (T_p_upper p hp.pos (moebiusFin p hp (↑σ) b₀).val)
```

Same matrix factorization as `orbit_lower_moebius`. τ has Gamma0Map = q where p·q ≡ M₁₁ ≡ Gamma0Map(σ) mod N. The unit product `Gamma0MapUnits(τ) · unitOfCoprime(p) = Gamma0MapUnits(σ)`. So `⟨τ⟩(⟨p⟩f) = ⟨σ⟩f` (diamond operators compose to give `⟨σ⟩`).

- [ ] **Step 2d: Add `orbit_lower_div_gamma0` — generalized lower→lower**

```lean
private theorem orbit_lower_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) ...
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hσ10 : (p : ℤ) ∣ M 1 0) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos)
```

Same matrix factorization as `orbit_rep_lower_div`. τ ∈ Gamma1(N) (since c ≡ 0 mod N from gcd(p,N)=1 and N|pσ₁₀). So `⟨τ⟩(⟨p⟩f) = ⟨p⟩f`. But we need `⟨p⟩f = ⟨p⟩(⟨σ⟩f)` on the RHS... actually `⟨τ⟩` is identity on Γ₁-forms, so `f|τ = f`. Then `(⟨p⟩f)|β_∞|σ = (⟨p⟩f)|τ|β_∞ = (⟨p⟩f)|β_∞`. And RHS is `(⟨p⟩(⟨σ⟩f))|β_∞`. These agree because τ ∈ Gamma1 acts trivially, and the Gamma0 action of σ on ⟨p⟩f combines correctly via diamond commutativity.

- [ ] **Step 2e: Verify all 4 lemmas compile**

Run `lean_diagnostic_messages` on the new section. Expected: 0 errors.

---

### Task 3: Prove `orbit_sum_comm` using the generalized lemmas

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean:1027`

The proof follows the SAME structure as `heckeT_p_slash_invariant` (Case 1 + Case 2), but using the Γ₀ orbit lemmas from Task 2. The diamond operators all collapse to `⟨σ⟩` by the `Gamma0MapUnits` tracking.

- [ ] **Step 3a: Distribute slash over the sum**

```lean
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set σ := (g : SL(2, ℤ))
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hσ_g0 : σ ∈ Gamma0 N := g.property
  simp only [heckeT_p_fun, heckeT_p_ut]
  rw [SlashAction.add_slash, sum_slash]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
```

- [ ] **Step 3b: Case split on p ∣ σ₁₀ and apply generalized orbit lemmas**

Same by_cases structure as `heckeT_p_slash_invariant`:
- Case 1 (p | σ₁₀): All upper terms go to upper via `orbit_upper_gamma0`, lower is fixed via `orbit_lower_div_gamma0`. Permute via `Finset.sum_equiv`.
- Case 2 (p ∤ σ₁₀): Find unique b₀ with p | A. Upper terms split: most go upper→upper, b₀ goes upper→lower. Lower goes lower→upper. Use `Finset.sum_ite_eq'` + `abel`.

The key difference from the Γ₁ proof: each orbit term produces `⟨σ⟩f` instead of `f`. So the permuted sum gives `∑ (⟨σ⟩f)|β_{φ(b)} = ∑ (⟨σ⟩f)|β_b`, and the diamond term gives `⟨p⟩(⟨σ⟩f)`. This matches the RHS `heckeT_p_fun k p hp hpN (diamondOpAux k g f)`.

Use `change` to convert ℚ-slash to ℝ-slash (via `monoidHomSlashAction`), then `← SlashAction.slash_mul` to combine, then apply the Γ₀ orbit lemmas.

- [ ] **Step 3c: Verify `orbit_sum_comm` compiles**

Run `lean_diagnostic_messages` on lines 1014-1028. Expected: 0 errors.

- [ ] **Step 3d: Final sorry count = 0**

Run `grep -c 'sorry' HeckeT_p.lean`. Expected: 0.

---

### Task 4: Refactor existing Γ₁ proofs to use Γ₀ lemmas (optional cleanup)

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`

The existing `heckeT_p_slash_invariant` can be simplified by using the Γ₀ orbit lemmas with the observation that for σ ∈ Γ₁(N) ≤ Γ₀(N), `diamondOpAux k ⟨σ, Gamma1_in_Gamma0 hσ⟩ f = f` (Γ₁ acts trivially via diamond). This would remove the need for the separate Γ₁-specific orbit lemmas.

- [ ] **Step 4a: Show `diamondOpAux` is trivial on Γ₁ elements**

Prove: `∀ σ ∈ Gamma1 N, diamondOpAux k ⟨σ, Gamma1_in_Gamma0 hσ⟩ f = f`.
This follows from `diamondOp_one` and `Gamma0MapUnits ⟨σ,_⟩ = 1` for σ ∈ Gamma1.

- [ ] **Step 4b: Rewrite `heckeT_p_slash_invariant` using Γ₀ lemmas**

Replace the Case 1 and Case 2 proofs with calls to the Γ₀ orbit lemmas, then simplify using the triviality of the diamond operator.

- [ ] **Step 4c: Remove the now-redundant Γ₁-specific orbit lemmas**

Delete `orbit_upper_moebius`, `orbit_rep_upper_coprime`, `orbit_rep_upper_div`, `orbit_rep_lower_coprime`, `orbit_lower_moebius`, `orbit_rep_lower_div` if they're no longer used.

- [ ] **Step 4d: Final build check**

Run `lake build` to verify the full project compiles. Expected: 0 errors.
