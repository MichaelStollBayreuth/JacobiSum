import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Jacobi Sums

This file defines the *Jacobi sum* of two multiplicative characters `χ` and `ψ` on a finite
commutative ring `R` with values in another commutative ring `R'`:

`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`

(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.

## References

We essentially follow
* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 8.3)][IrelandRosen1990]

but generalize where appropriate.

This is based on Lean code written as part of the bachelor's thesis of Alexander Spahl.
-/

open BigOperators Finset

/-!
### Gauss and Jacobi sums of characters with values in ℂ
-/

section complex_valued

variable {F : Type*} [Fintype F] [Field F]

/--  The Gauss sum of a multiplicative character on a finite field `F` with values in `ℂ`
has absolute value the square root of `#F`. -/
lemma gaussSum_abs_eq_sqrt {χ : MulChar F ℂ} (hχ : χ ≠ 1) {φ : AddChar F ℂ}
    (hφ : φ.IsPrimitive) :
    Complex.abs (gaussSum χ φ) = Real.sqrt (Fintype.card F) := by
  have hF : 0 < ringChar F := Nat.pos_of_ne_zero <| CharP.ringChar_ne_zero_of_finite F
  have gauss_inv : gaussSum χ⁻¹ φ⁻¹ = star (gaussSum χ φ) := by
    rw [← χ.star_eq_inv, gaussSum, gaussSum]
    simp only [MulChar.star_apply, RCLike.star_def, star_sum, star_mul', AddChar.starComp_apply hF]
  have := gaussSum_mul_gaussSum_eq_card hχ hφ
  rw [gauss_inv, Complex.star_def, Complex.mul_conj] at this
  norm_cast at this
  rw [← Real.sqrt_inj (Complex.normSq_nonneg (gaussSum _ _)) (Nat.cast_nonneg _)] at this
  rw [← this]
  rfl

/-- If `χ`, `ψ` and `χψ` are all nontrivial multiplicative characters on a finite field `F`
with values in `ℂ`, then `|J(χ,ψ)| = √#F`. -/
theorem jacobiSum_abs_eq_sqrt [DecidableEq F] {χ ψ : MulChar F ℂ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ * ψ ≠ 1) :
    Complex.abs (jacobiSum χ ψ) = Real.sqrt (Fintype.card F) := by
  -- rewrite jacobiSum as gaussSums
  let φ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hφ : φ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h : (Fintype.card F : ℂ) ≠ 0 := by
    norm_cast
    simp only [Fintype.card_ne_zero, not_false_eq_true]
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum h hχψ hφ, map_div₀, map_mul]
  -- rewrite each absolute value of a gaussSum as `√#F`
  rw [gaussSum_abs_eq_sqrt hχ hφ, gaussSum_abs_eq_sqrt hψ hφ, gaussSum_abs_eq_sqrt hχψ hφ]
  simp only [Nat.cast_nonneg, Real.mul_self_sqrt, Real.div_sqrt]

end complex_valued

/-!
### A proof of Fermat's two-squares theorem via Jacobi sums
-/
-- count_heartbeats in -- 4693
open MulChar in
/-- An alternative proof of the sum-of-two-squares-theorem using Jacobi sums. -/
theorem Nat.prime_sq_add_sq' {p : ℕ} [hp : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, p = a ^ 2 + b ^ 2 := by
  -- character `χ` of order 4 with values in `ℤ[i]`
  have hp' : 4 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card p, ← hp]
    exact Nat.dvd_sub_mod p
  have hI : IsPrimitiveRoot (⟨0, 1⟩ : GaussianInt) 4 := by
    have : orderOf (⟨0, 1⟩ : GaussianInt) = 4 :=
      (orderOf_eq_iff <| zero_lt_succ _).mpr ⟨rfl, by decide⟩
    exact this ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨χ, hχ⟩ := exists_mulChar_orderOf (ZMod p) hp' hI
  have h₁ : 1 < orderOf χ := by rw [hχ]; norm_num
  have h₂ : 2 < orderOf χ := by rw [hχ]; norm_num
  have hχ₁ := pow_one χ ▸ pow_ne_one_of_lt_orderOf one_ne_zero h₁
  have hχ₂ := pow_two χ ▸ pow_ne_one_of_lt_orderOf two_ne_zero h₂
  let f := GaussianInt.toComplex
  have hJ := jacobiSum_ringHomComp χ χ f
  have hχ₁' := (MulChar.ringHomComp_ne_one_iff GaussianInt.toComplex_injective).mpr hχ₁
  have hχ₂' : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff GaussianInt.toComplex_injective).mpr hχ₂
  have := jacobiSum_abs_eq_sqrt hχ₁' hχ₁' hχ₂'
  rw [hJ] at this
  apply_fun (· ^ 2) at this
  simp only [Int.reduceNeg, Complex.sq_abs, ZMod.card, cast_nonneg, Real.sq_sqrt] at this
  rw [← GaussianInt.intCast_real_norm, Zsqrtd.norm] at this
  norm_cast at this
  simp only [Int.reduceNeg, ← sq, Int.reduceNegSucc, neg_mul, one_mul, sub_neg_eq_add] at this
  exact ⟨_, _, this.symm⟩
