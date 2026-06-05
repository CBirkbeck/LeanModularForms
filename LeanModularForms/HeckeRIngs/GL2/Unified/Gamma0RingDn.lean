/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0

/-!
# Ring-side Hecke elements `D_n` in `𝕋(Γ₀(N))`

This file is the **ring layer** of the ring-first Hecke-operator architecture: it defines,
purely inside the Hecke ring `𝕋 (Gamma0_pair N) ℤ` (commutative by Shimura Prop 3.8 for
`Γ₀(N)`, via the Atkin–Lehner anti-involution), the elements whose images under the
character-space ring homomorphisms *are* the classical Hecke operators:

* `heckeRingDp p`     — the prime class `Γ₀(N)·diag(1,p)·Γ₀(N)` (defined for **all** `p > 0`,
  including the bad primes `p ∣ N`);
* `heckeRingSpp p`    — the scalar class `Γ₀(N)·diag(p,p)·Γ₀(N)` for `p ∤ N`, and `0` for
  `p ∣ N` (the scalar matrix `diag(p,p)` does not lie in `Δ₀(N)` when `p ∣ N`; the junk
  value `0` mirrors the vanishing of the diamond operator `⟨p⟩` there);
* `heckeRingD_ppow p r` — the prime-power element defined by the Diamond–Shurman
  recurrence `D_{p^{r+2}} = D_p·D_{p^{r+1}} − (p·S_p)·D_{p^r}`, which for `p ∣ N`
  degenerates (since `S_p = 0`) to `D_{p^r} = D_p^r`;
* `heckeRingD_n n`    — the composite element, assembled multiplicatively over the prime
  factorisation of `n` by `minFac`-peeling, with **genuine** bad-prime factors.

The structural identities — commutativity (free), the per-prime product formula
`D_{p^r}·D_{p^s} = ∑_{i ≤ min(r,s)} (p·S_p)^i · D_{p^{r+s−2i}}`, and coprime
multiplicativity `D_m·D_n = D_{mn}` — are **pure commutative algebra**: they are proven
below for an arbitrary commutative ring (the `Formal*` sections) and then instantiated at
`𝕋 (Gamma0_pair N) ℤ`.  No operators, coset combinatorics, or analytic input appear.
The operator-level counterparts (`heckeT_n_comm`, `heckeT_n_mul_coprime`, …) are then
*transported* along `heckeRingHomCharSpace` and glued over the character direct sum,
replacing their former self-contained induction cascades.

## Main definitions

* `HeckeRing.GL2.Unified.heckeRingSpp`
* `HeckeRing.GL2.Unified.heckeRingD_ppow`
* `HeckeRing.GL2.Unified.heckeRingD_n`
* `HeckeRing.GL2.Unified.heckeRingS_n` — the composite scalar class `S_d` (multiplicative
  in `d`; vanishes unless `d` is coprime to `N`), the ring-side avatar of `d^{k-2}·⟨d⟩`.

## Main results

* `heckeRingD_ppow_mul`  — the per-prime product formula (Chebyshev-style algebra).
* `heckeRingD_n_mul_coprime` — `D_{mn} = D_m · D_n` for coprime `m, n`.
-/

namespace HeckeRing.GL2.Unified

open HeckeRing HeckeRing.GLn

/-! ## Formal commutative algebra

The recurrence and peeling constructions, over an arbitrary commutative ring.  Everything
here is instance-clean: `𝕋 (Gamma0_pair N) ℤ` carries both a global `Ring` instance and a
(non-instance) `CommRing` structure `instCommRing_Gamma0`, and stating the algebra
generically avoids ever mixing the two elaboration paths. -/

section FormalChebyshev

variable {R : Type*} [CommRing R]

/-- Formal rank-one product step: if `d` satisfies the Hecke recurrence
`d (r+2) = D·d (r+1) − S·d r`, then `D · d m = d (m+1) + S · d (m−1)` for `m ≥ 1`. -/
private theorem formal_D_mul_d (D S : R) (d : ℕ → R)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) (m : ℕ) (hm : 0 < m) :
    D * d m = d (m + 1) + S * d (m - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show m + 1 + 1 = m + 2 from rfl, hrec m, Nat.add_sub_cancel]
  ring

/-- **Formal Chebyshev-style product formula**: if `d 0 = 1`, `d 1 = D` and
`d (r+2) = D·d (r+1) − S·d r`, then for `r ≤ s`
`d r · d s = ∑_{i=0}^{r} S^i · d (r+s−2i)`. -/
private theorem formal_ppow_mul (D S : R) (d : ℕ → R) (h0 : d 0 = 1) (h1 : d 1 = D)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    ∀ r s : ℕ, r ≤ s →
      d r * d s = ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s hrs
    match r, ih with
    | 0, _ => simp [h0]
    | 1, _ =>
      rw [h1, formal_D_mul_d D S d hrec s (by omega),
        Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_mul, pow_one,
        show 1 + s - 2 * 0 = s + 1 by omega, show 1 + s - 2 * 1 = s - 1 by omega]
    | (r + 2), ih =>
      have key : ∀ i ∈ Finset.range (r + 2),
          D * (S ^ i * d (r + 1 + s - 2 * i)) =
            S ^ i * d (r + 2 + s - 2 * i) + S ^ (i + 1) * d (r + s - 2 * i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have h := formal_D_mul_d D S d hrec (r + 1 + s - 2 * i) (by omega)
        rw [show r + 1 + s - 2 * i + 1 = r + 2 + s - 2 * i by omega,
          show r + 1 + s - 2 * i - 1 = r + s - 2 * i by omega] at h
        calc D * (S ^ i * d (r + 1 + s - 2 * i))
            = S ^ i * (D * d (r + 1 + s - 2 * i)) := by ring
          _ = S ^ i * (d (r + 2 + s - 2 * i) + S * d (r + s - 2 * i)) := by rw [h]
          _ = _ := by ring
      have hL : d (r + 2) * d s = D * (d (r + 1) * d s) - S * (d r * d s) := by
        rw [hrec r]; ring
      rw [hL, ih (r + 1) (by omega) s (by omega), ih r (by omega) s (by omega),
        Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib]
      have hshift : S * ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) =
          ∑ i ∈ Finset.range (r + 1), S ^ (i + 1) * d (r + s - 2 * i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hshift, Finset.sum_range_succ (fun i ↦ S ^ (i + 1) * d (r + s - 2 * i)) (r + 1),
        Finset.sum_range_succ (fun i ↦ S ^ i * d (r + 2 + s - 2 * i)) (r + 2),
        show r + 2 + s - 2 * (r + 2) = r + s - 2 * (r + 1) by omega]
      ring

end FormalChebyshev

section FormalPeel

variable {R : Type*} [Monoid R]

/-- The `minFac`-peeling product: `peelProd f n = f p v · peelProd f (n / p^v)` where
`p = minFac n` and `v = v_p(n)`, with `peelProd f 0 = peelProd f 1 = 1`.  The block map
`f : ℕ → ℕ → R` is only ever evaluated at `(p, v_p(n))` with `p` prime. -/
private noncomputable def peelProd (f : ℕ → ℕ → R) (n : ℕ) : R :=
  if h : n ≤ 1 then 1
  else
    let p := n.minFac
    let v := n.factorization p
    f p v * peelProd f (n / p ^ v)
termination_by n
decreasing_by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)).ne' hp.one_lt)

@[simp] private theorem peelProd_zero (f : ℕ → ℕ → R) : peelProd f 0 = 1 := by
  rw [peelProd]; simp

@[simp] private theorem peelProd_one (f : ℕ → ℕ → R) : peelProd f 1 = 1 := by
  rw [peelProd]; simp

private theorem peelProd_peel (f : ℕ → ℕ → R) (n : ℕ) (hn : 1 < n) :
    peelProd f n =
      f n.minFac (n.factorization n.minFac) *
        peelProd f (n / n.minFac ^ n.factorization n.minFac) := by
  conv_lhs => rw [peelProd]
  rw [dif_neg (by omega : ¬ n ≤ 1)]

/-- `peelProd` over a prime power is a single block. -/
private theorem peelProd_ppow (f : ℕ → ℕ → R) {p : ℕ} (hp : Nat.Prime p) (v : ℕ)
    (hv : 0 < v) : peelProd f (p ^ v) = f p v := by
  have h1 : 1 < p ^ v := Nat.one_lt_pow hv.ne' hp.one_lt
  have hminFac : (p ^ v).minFac = p := hp.pow_minFac hv.ne'
  have hfact : (p ^ v).factorization p = v := by
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  rw [peelProd_peel f _ h1, hminFac, hfact, Nat.div_self (pow_pos hp.pos v),
    peelProd_one, mul_one]

end FormalPeel

section FormalPeelComm

variable {R : Type*} [CommMonoid R]

/-- **`peelProd` is multiplicative on coprime arguments** — for any block map `f`.
Pure commutative algebra: the blocks of `m·n` are the disjoint union of the blocks of
`m` and `n`, and commutativity reorders the product. -/
private theorem peelProd_mul_coprime (f : ℕ → ℕ → R) :
    ∀ m n : ℕ, Nat.Coprime m n → peelProd f (m * n) = peelProd f m * peelProd f n := by
  -- Strong induction on the product `m * n`.
  suffices H : ∀ t m n : ℕ, m * n = t → Nat.Coprime m n →
      peelProd f (m * n) = peelProd f m * peelProd f n by
    exact fun m n h ↦ H (m * n) m n rfl h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro m n hmn hcop
    -- Degenerate cases: a factor ≤ 1 (coprimality forces the other to be 1 when one is 0).
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hcop; subst hcop; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hcop; subst hcop; simp
    rcases eq_or_ne m 1 with rfl | hm1'
    · rw [one_mul, peelProd_one, one_mul]
    rcases eq_or_ne n 1 with rfl | hn1'
    · rw [mul_one, peelProd_one, mul_one]
    have hm1 : 1 < m := by omega
    have hn1 : 1 < n := by omega
    -- Both factors exceed 1.  Peel the smallest prime `q` of `m*n`; it divides exactly
    -- one of the factors, and the two branches are symmetric.
    have hmn1 : 1 < m * n := by
      calc 1 < m := hm1
      _ ≤ m * n := Nat.le_mul_of_pos_right m hn
    set q := (m * n).minFac with hq_def
    have hq : Nat.Prime q := Nat.minFac_prime (by omega)
    have hq_dvd : q ∣ m * n := Nat.minFac_dvd _
    rcases (Nat.Prime.dvd_mul hq).mp hq_dvd with hqm | hqn
    · -- `q ∣ m`: the `q`-block of `m*n` is the `q`-block of `m`.
      have hqn' : ¬ q ∣ n := fun hqn ↦
        hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqm hqn))
      have hfac : (m * n).factorization q = m.factorization q := by
        rw [Nat.factorization_mul hm.ne' hn.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hqn']
      have hvq : 0 < m.factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq hm.ne' hqm
      have hq_min_m : m.minFac = q := by
        refine le_antisymm (Nat.minFac_le_of_dvd hq.two_le hqm) ?_
        rw [hq_def]
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : m ≠ 1)).two_le
          ((Nat.minFac_dvd m).trans (Dvd.intro n rfl))
      set v := m.factorization q with hv_def
      obtain ⟨m', hm'⟩ : q ^ v ∣ m := Nat.ordProj_dvd m q
      have hqv1 : 1 < q ^ v := Nat.one_lt_pow hvq.ne' hq.one_lt
      have hm'_pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with rfl | h
        · rw [mul_zero] at hm'; omega
        · exact h
      have hdiv_m : m / q ^ v = m' := by
        rw [hm']; exact Nat.mul_div_cancel_left m' (by positivity)
      have hdiv_mn : m * n / q ^ v = m' * n := by
        rw [hm', mul_assoc]; exact Nat.mul_div_cancel_left _ (by positivity)
      have hcop' : Nat.Coprime m' n :=
        Nat.Coprime.coprime_dvd_left ⟨q ^ v, by rw [hm']; ring⟩ hcop
      have hm'_lt : m' < m := by
        rw [hm']; exact (Nat.lt_mul_iff_one_lt_left hm'_pos).mpr hqv1
      have hlt : m' * n < t := by
        rw [← hmn]; exact Nat.mul_lt_mul_of_lt_of_le hm'_lt le_rfl hn
      rw [peelProd_peel f (m * n) hmn1, ← hq_def, hfac, hdiv_mn,
        peelProd_peel f m hm1, hq_min_m, ← hv_def, hdiv_m,
        ih (m' * n) hlt m' n rfl hcop', mul_assoc]
    · -- `q ∣ n`: symmetric, with a `mul_left_comm` to reorder the blocks.
      have hqm' : ¬ q ∣ m := fun hqm ↦
        hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqm hqn))
      have hfac : (m * n).factorization q = n.factorization q := by
        rw [Nat.factorization_mul hm.ne' hn.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hqm']
      have hvq : 0 < n.factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq hn.ne' hqn
      have hq_min_n : n.minFac = q := by
        refine le_antisymm (Nat.minFac_le_of_dvd hq.two_le hqn) ?_
        rw [hq_def]
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : n ≠ 1)).two_le
          ((Nat.minFac_dvd n).trans (Dvd.intro_left m rfl))
      set v := n.factorization q with hv_def
      obtain ⟨n', hn'⟩ : q ^ v ∣ n := Nat.ordProj_dvd n q
      have hqv1 : 1 < q ^ v := Nat.one_lt_pow hvq.ne' hq.one_lt
      have hn'_pos : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with rfl | h
        · rw [mul_zero] at hn'; omega
        · exact h
      have hdiv_n : n / q ^ v = n' := by
        rw [hn']; exact Nat.mul_div_cancel_left n' (by positivity)
      have hdiv_mn : m * n / q ^ v = m * n' := by
        rw [hn', show m * (q ^ v * n') = q ^ v * (m * n') by ring]
        exact Nat.mul_div_cancel_left _ (by positivity)
      have hcop' : Nat.Coprime m n' :=
        Nat.Coprime.coprime_dvd_right ⟨q ^ v, by rw [hn']; ring⟩ hcop
      have hn'_lt : n' < n := by
        rw [hn']; exact (Nat.lt_mul_iff_one_lt_left hn'_pos).mpr hqv1
      have hlt : m * n' < t := by
        rw [← hmn]; exact Nat.mul_lt_mul_of_le_of_lt le_rfl hn'_lt hm
      rw [peelProd_peel f (m * n) hmn1, ← hq_def, hfac, hdiv_mn,
        peelProd_peel f n hn1, hq_min_n, ← hv_def, hdiv_n,
        ih (m * n') hlt m n' rfl hcop', mul_left_comm]

end FormalPeelComm

variable {N : ℕ} [NeZero N]

/-! ## The ring elements -/

/-- The ring-side prime generator: the single double coset `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)`.
Defined for every `p > 0`, including bad primes `p ∣ N`. -/
noncomputable def heckeRingDp (p : ℕ) (hp : 0 < p) : 𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp) 1

/-- The ring-side scalar generator: the single scalar double coset `T(p,p)` for `p ∤ N`,
and `0` for `p ∣ N` (where `diag(p,p) ∉ Δ₀(N)`; the vanishing mirrors `⟨p⟩ = 0`). -/
noncomputable def heckeRingSpp (p : ℕ) (hp : Nat.Prime p) : 𝕋 (Gamma0_pair N) ℤ :=
  if hpN : Nat.Coprime p N then
    T_single (Gamma0_pair N) ℤ (T_diag_Gamma0 N (fun _ : Fin 2 ↦ p) (fun _ ↦ hp.pos)
      (by rw [Int.gcd_natCast_natCast]; exact hpN)) 1
  else 0

@[simp] theorem heckeRingSpp_of_not_coprime (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) : heckeRingSpp (N := N) p hp = 0 :=
  dif_neg hpN

/-- The ring-side prime-power element, defined by the Diamond–Shurman recurrence
`D_{p^0} = 1`, `D_{p^1} = D_p`, and
`D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p·S_p) · D_{p^r}`.
For `p ∣ N` the scalar term vanishes and the recurrence degenerates to `D_{p^r} = D_p^r`. -/
noncomputable def heckeRingD_ppow (p : ℕ) (hp : Nat.Prime p) :
    ℕ → 𝕋 (Gamma0_pair N) ℤ
  | 0 => 1
  | 1 => heckeRingDp p hp.pos
  | r + 2 =>
    heckeRingDp p hp.pos * heckeRingD_ppow p hp (r + 1) -
      ((p : ℤ) • heckeRingSpp p hp) * heckeRingD_ppow p hp r

@[simp] theorem heckeRingD_ppow_zero (p : ℕ) (hp : Nat.Prime p) :
    heckeRingD_ppow (N := N) p hp 0 = 1 := rfl

@[simp] theorem heckeRingD_ppow_one (p : ℕ) (hp : Nat.Prime p) :
    heckeRingD_ppow (N := N) p hp 1 = heckeRingDp p hp.pos := rfl

theorem heckeRingD_ppow_succ_succ (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    heckeRingD_ppow (N := N) p hp (r + 2) =
      heckeRingDp p hp.pos * heckeRingD_ppow p hp (r + 1) -
        ((p : ℤ) • heckeRingSpp p hp) * heckeRingD_ppow p hp r := rfl

/-- For a bad prime `p ∣ N` the recurrence degenerates: `D_{p^r} = D_p^r`. -/
theorem heckeRingD_ppow_eq_pow_of_not_coprime (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeRingD_ppow (N := N) p hp r = heckeRingDp p hp.pos ^ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (r + 2), ih =>
      rw [heckeRingD_ppow_succ_succ, heckeRingSpp_of_not_coprime p hp hpN,
        smul_zero, zero_mul, sub_zero, ih (r + 1) (by omega)]
      exact (pow_succ' _ _).symm

/-- **Per-prime product formula** (Shimura 3.24(3) at level `Γ₀(N)`, ring side): for
`r ≤ s`,
`D_{p^r} · D_{p^s} = ∑_{i=0}^{r} (p·S_p)^i · D_{p^{r+s−2i}}`.
Instantiates the formal Chebyshev identity in the commutative ring `𝕋 (Gamma0_pair N) ℤ`.
For `p ∣ N` both sides collapse to `D_p^{r+s}`. -/
theorem heckeRingD_ppow_mul (p : ℕ) (hp : Nat.Prime p) (r s : ℕ) (hrs : r ≤ s) :
    heckeRingD_ppow (N := N) p hp r * heckeRingD_ppow p hp s =
      ∑ i ∈ Finset.range (r + 1),
        ((p : ℤ) • heckeRingSpp p hp) ^ i * heckeRingD_ppow p hp (r + s - 2 * i) := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact formal_ppow_mul (heckeRingDp p hp.pos) ((p : ℤ) • heckeRingSpp p hp)
    (heckeRingD_ppow p hp) rfl rfl (fun r ↦ heckeRingD_ppow_succ_succ p hp r) r s hrs

/-- The composite ring element `D_n`, assembled by `minFac`-peeling over the prime
factorisation of `n` — with **genuine** factors at bad primes `p ∣ N`
(`D_{p^v} = D_p^v`). `D_0 = D_1 = 1`. -/
noncomputable def heckeRingD_n (n : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingD_ppow p hp v else 1) n

@[simp] theorem heckeRingD_n_zero : heckeRingD_n (N := N) 0 = 1 := peelProd_zero _

@[simp] theorem heckeRingD_n_one : heckeRingD_n (N := N) 1 = 1 := peelProd_one _

/-- On a prime power, the composite assembly agrees with the prime-power element. -/
theorem heckeRingD_n_ppow (p : ℕ) (hp : Nat.Prime p) (v : ℕ) :
    heckeRingD_n (N := N) (p ^ v) = heckeRingD_ppow p hp v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  rw [heckeRingD_n, peelProd_ppow _ hp v hv, dif_pos hp]

theorem heckeRingD_n_peel (n : ℕ) (hn : 1 < n) :
    heckeRingD_n (N := N) n =
      heckeRingD_ppow n.minFac (Nat.minFac_prime (by omega : n ≠ 1))
          (n.factorization n.minFac) *
        heckeRingD_n (n / n.minFac ^ n.factorization n.minFac) := by
  rw [heckeRingD_n, peelProd_peel _ n hn, dif_pos (Nat.minFac_prime (by omega : n ≠ 1))]
  rfl

/-- **Coprime multiplicativity** (ring side): `D_{mn} = D_m · D_n` for coprime `m, n`. -/
theorem heckeRingD_n_mul_coprime (m n : ℕ) (hmn : Nat.Coprime m n) :
    heckeRingD_n (N := N) (m * n) = heckeRingD_n m * heckeRingD_n n := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact peelProd_mul_coprime _ m n hmn

/-- The composite scalar class `S_d`: multiplicative over the factorisation of `d`,
with `S_{p^v} = S_p^v`.  Vanishes (some factor is `0`) unless `d` is coprime to `N`.
Ring-side avatar of the operator `d ↦ d^{k-2}·⟨d⟩`. -/
noncomputable def heckeRingS_n (d : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingSpp p hp ^ v else 1) d

@[simp] theorem heckeRingS_n_one : heckeRingS_n (N := N) 1 = 1 := peelProd_one _

end HeckeRing.GL2.Unified
