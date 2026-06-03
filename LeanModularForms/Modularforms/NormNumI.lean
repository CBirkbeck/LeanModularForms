/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
module

public import Mathlib.Data.Complex.Basic

@[expose] public section

/-!
# `norm_numI`: a `norm_num`-style extension for complex numerals

This file implements a `norm_num` extension and a `conv`-mode tactic `norm_numI`
that reduce closed complex expressions built from `0`, `1`, `I`, scientific
literals, `+`, `-`, `*`, `⁻¹`, `/`, conjugation, and natural-number powers to
their normal form `⟨a, b⟩` with `a, b : ℝ`. The companion `norm_num` extensions
decide equalities `(z : ℂ) = (w : ℂ)` and reduce `Complex.re z` / `Complex.im z`
to the same normal form.
-/

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta
namespace NormNumI

theorem split_I : I = ⟨0, 1⟩ := rfl

theorem split_zero : (0 : ℂ) = ⟨0, 0⟩ := rfl

theorem split_one : (1 : ℂ) = ⟨1, 0⟩ := rfl

theorem split_add {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ}
    (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ + z₂ = ⟨(a₁ + a₂), (b₁ + b₂)⟩ := h₁ ▸ h₂ ▸ rfl

theorem split_mul {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ * z₂ = ⟨(a₁ * a₂ - b₁ * b₂), (a₁ * b₂ + b₁ * a₂)⟩ := by
  subst h₁; subst h₂
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem split_inv {z : ℂ} {x y : ℝ} (h : z = ⟨x, y⟩) :
    z⁻¹ = ⟨x / (x * x + y * y), - y / (x * x + y * y)⟩ := by
  subst h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem split_neg {z : ℂ} {a b : ℝ} (h : z = ⟨a, b⟩) :
    -z = ⟨-a, -b⟩ := h ▸ rfl

theorem split_conj {w : ℂ} {a b : ℝ} (hw : w = ⟨a, b⟩) :
    conj w = ⟨a, -b⟩ := hw ▸ rfl

theorem split_num (n : ℕ) [n.AtLeastTwo] :
    OfNat.ofNat (α := ℂ) n = ⟨OfNat.ofNat n, 0⟩ := rfl

theorem split_scientific (m exp : ℕ) (x : Bool) :
    (OfScientific.ofScientific m x exp : ℂ) = ⟨(OfScientific.ofScientific m x exp : ℝ), 0⟩ :=
  rfl

theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : z = ⟨a, b⟩)
    (pf_a : a = a') (pf_b : b = b') : z = ⟨a', b'⟩ := by simp_all

theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az = aw) (hb : bz = bw) : z = w := by
  simp [hz, hw, ha, hb]

theorem ne_of_re_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az ≠ aw) : z ≠ w := by
  simp [hz, hw, ha]

theorem ne_of_im_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (hb : bz ≠ bw) : z ≠ w := by
  simp [hz, hw, hb]

theorem re_eq_of_eq {z : ℂ} {a b : ℝ} (hz : z = ⟨a, b⟩) : Complex.re z = a := by simp [hz]
theorem im_eq_of_eq {z : ℂ} {a b : ℝ} (hz : z = ⟨a, b⟩) : Complex.im z = b := by simp [hz]

meta partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  match z with
  /- parse an addition: `z₁ + z₂` -/
  | ~q($z₁ + $z₂) =>
    let ⟨a₁, b₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, pf₂⟩ ← parse z₂
    pure ⟨q($a₁ + $a₂), q($b₁ + $b₂), q(split_add $pf₁ $pf₂)⟩
  /- parse a multiplication: `z₁ * z₂` -/
  | ~q($z₁ * $z₂) =>
    let ⟨a₁, b₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, pf₂⟩ ← parse z₂
    pure ⟨q($a₁ * $a₂ - $b₁ * $b₂), q($a₁ * $b₂ + $b₁ * $a₂), q(split_mul $pf₁ $pf₂)⟩
  /- parse an inversion: `z⁻¹` -/
  | ~q($z⁻¹) =>
    let ⟨x, y, pf⟩ ← parse z
    pure ⟨q($x / ($x * $x + $y * $y)), q(-$y / ($x * $x + $y * $y)), q(split_inv $pf)⟩
  /- parse `z₁/z₂` -/
  | ~q($z₁ / $z₂) => parse q($z₁ * $z₂⁻¹)
  /- parse `-z` -/
  | ~q(-$w) =>
    let ⟨a, b, pf⟩ ← parse w
    pure ⟨q(-$a), q(-$b), q(split_neg $pf)⟩
  /- parse a subtraction `z₁ - z₂` -/
  | ~q($z₁ - $z₂) => parse q($z₁ + -$z₂)
  /- parse conjugate `conj z` -/
  | ~q(conj $w) =>
    let ⟨a, b, pf⟩ ← parse w
    return ⟨q($a), q(-$b), q(split_conj $pf)⟩
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n) =>
    match n.nat? with
    | some 0 =>
      return ⟨q(1), q(0), (q(pow_zero $w) :)⟩
    | some (n + 1) => parse q($w ^ $n * $w)
    | none => throwError "exponent {n} not handled by norm_numI"
  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨q(0), q(1), q(split_I)⟩
  /- anything else needs to be on the list of atoms -/
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n := n.rawNatLit? | throwError "{n} is not a natural number"
    if n == 0 then
      return ⟨q(0), q(0), (q(split_zero):)⟩
    else if n == 1 then
      return ⟨q(1), q(0), (q(split_one):)⟩
    else
      let _i : Q(Nat.AtLeastTwo $n) ← synthInstanceQ q(Nat.AtLeastTwo $n)
      return ⟨q(OfNat.ofNat $n), q(0), (q(split_num $n):)⟩
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    return ⟨q(OfScientific.ofScientific $m $x $exp), q(0), q(split_scientific _ _ _)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

meta def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) b
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

-- Testing the `parse` function
elab "norm_numI_parse" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← parse z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

end NormNumI

namespace NormNum

/-- The `norm_num` extension which identifies expressions of the form `(z : ℂ) = (w : ℂ)`,
such that `norm_num` successfully recognises both the real and imaginary parts of both `z` and `w`.
-/
@[norm_num (_ : ℂ) = _] meta def evalComplexEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f z) w ← whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq f q(Eq (α := ℂ))
  have z : Q(ℂ) := z
  have w : Q(ℂ) := w
  haveI' : $e =Q ($z = $w) := ⟨⟩
  let ⟨az, bz, pfz⟩ ← NormNumI.parse z
  let ⟨aw, bw, pfw⟩ ← NormNumI.parse w
  let ⟨ba, ra⟩ ← deriveBool q($az = $aw)
  match ba with
  | true =>
    let ⟨bb, rb⟩ ← deriveBool q($bz = $bw)
    match bb with
    | true => return Result'.isBool true q(NormNumI.eq_of_eq_of_eq_of_eq $pfz $pfw $ra $rb)
    | false => return Result'.isBool false q(NormNumI.ne_of_im_ne $pfz $pfw $rb)
  | false => return Result'.isBool false q(NormNumI.ne_of_re_ne $pfz $pfw $ra)

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] meta def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 0 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.re $z) := ⟨⟩
  let ⟨a, _, pf⟩ ← NormNumI.parse z
  let r ← derive q($a)
  return r.eqTrans q(NormNumI.re_eq_of_eq $pf)

/-- The `norm_num` extension which identifies expressions of the form `Complex.im (z : ℂ)`,
such that `norm_num` successfully recognises the imaginary part of `z`.
-/
@[norm_num Complex.im _] meta def evalIm : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 1 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.im $z) := ⟨⟩
  let ⟨_, b, pf⟩ ← NormNumI.parse z
  let r ← derive q($b)
  return r.eqTrans q(NormNumI.im_eq_of_eq $pf)

end NormNum

end Mathlib.Meta
