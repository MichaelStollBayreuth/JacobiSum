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
### Jacobi sums over finite fields
-/


section GaussSum

variable {F R : Type*} [Fintype F] [Field F] [CommRing R]

lemma mul_gaussSum_inv_eq_gaussSum (χ : MulChar F R) (ψ : AddChar F R) :
    χ (-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ := by
  rw [ψ.inv_mulShift, ← Units.coe_neg_one]
  exact gaussSum_mulShift χ ψ (-1)

open MulChar FiniteField

/-- If `χ` is a multiplicative character of order `n` on a finite field `F`,
then `g(χ) * g(χ^(n-1)) = χ(-1)*#F` -/
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one [IsDomain R] {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ (orderOf χ - 1)) ψ = χ (-1) * Fintype.card F := by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one]
  rw [h, ← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm, gaussSum_mul_gaussSum_eq_card hχ hψ,
    inv_apply', inv_neg_one]

/-- If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`. -/
theorem gaussSum_pow_eq_prod_jacobiSum [DecidableEq F] [IsDomain R] {χ : MulChar F R}
    {ψ : AddChar F R} (hχ : 2 ≤ orderOf χ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ orderOf χ =
      χ (-1) * Fintype.card F * ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) := by
  -- show `g(χ)^i = g(χ^i) * J(χ,χ)*...*J(χ,χ^(i-1))` for `1 ≤ i < n` by induction
  let n := orderOf χ
  have pow_gauss' : ∀ i ∈ Ico 1 n, (gaussSum χ ψ) ^ i =
      gaussSum (χ ^ i) ψ * ∏ j ∈ Ico 1 i, jacobiSum χ (χ ^ j) := by
    intro i hi
    obtain ⟨one_le_i, i_lt_n⟩ := mem_Ico.mp hi; clear hi -- otherwise error below
    induction i, one_le_i using Nat.le_induction with
    | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
    | succ i hi ih =>
        specialize ih <| lt_trans (Nat.lt_succ_self i) i_lt_n
        have gauss_rw : gaussSum (χ ^ i) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ i) * gaussSum (χ ^ (i + 1)) ψ := by
          have hχi : χ * (χ ^ i) ≠ 1 :=
            pow_succ' χ i ▸ pow_ne_one_of_lt_orderOf i.add_one_ne_zero i_lt_n
          rw [mul_comm, ← jacobiSum_mul_nontrivial hχi, mul_comm, ← pow_succ']
        apply_fun (· * gaussSum χ ψ) at ih
        rw [mul_right_comm, ← pow_succ, gauss_rw] at ih
        rw [ih, Finset.prod_Ico_succ_top hi, mul_rotate, mul_assoc]
  -- get equality for `i = n-1`
  have gauss_pow_n_sub := pow_gauss' (n - 1) (by simp only [mem_Ico]; omega)
  apply_fun (gaussSum χ ψ * .) at gauss_pow_n_sub
  rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos (by omega)] at gauss_pow_n_sub
  have hχ₁ : χ ≠ 1 :=
    fun h ↦ ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [gauss_pow_n_sub, ← mul_assoc, gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

end GaussSum

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

open MulChar in
/-- An alternative proof of the sum-of-two-squares-theorem using Jacobi sums. -/
theorem Nat.prime_sq_add_sq' {p : ℕ} [hp : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, p = a ^ 2 + b ^ 2 := by
  -- character `χ` of order 4 with values in `ℤ[i]`
  have hp' : 4 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    exact hp ▸ Nat.dvd_sub_mod p
  have hI : IsPrimitiveRoot (⟨0, 1⟩ : GaussianInt) 4 := by
    convert ← IsPrimitiveRoot.orderOf ?_
    rw [orderOf_eq_iff (by norm_num)]
    exact ⟨rfl, by decide⟩
  obtain ⟨χ, hχ⟩ := exists_mulChar_orderOf (ZMod p) hp' hI
  have h₁ : 1 < orderOf χ := by rw [hχ]; norm_num
  have h₂ : 2 < orderOf χ := by rw [hχ]; norm_num
  have hχ₁ := pow_ne_one_of_lt_orderOf one_ne_zero h₁
  rw [pow_one] at hχ₁
  have hχ₂ := pow_ne_one_of_lt_orderOf two_ne_zero h₂
  rw [pow_two] at hχ₂
  let f : GaussianInt →+* ℂ := GaussianInt.toComplex
  have hJ := jacobiSum_ringHomComp χ χ f
  have hχ₁' := (MulChar.ringHomComp_ne_one_iff GaussianInt.toComplex_injective).mpr hχ₁
  have hχ₂' : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    convert (MulChar.ringHomComp_ne_one_iff GaussianInt.toComplex_injective).mpr hχ₂
    ext1
    simp only [Int.reduceNeg, coeToFun_mul, Pi.mul_apply, ringHomComp_apply, map_mul]
  have := jacobiSum_abs_eq_sqrt hχ₁' hχ₁' hχ₂'
  rw [hJ] at this
  apply_fun (· ^ 2) at this
  simp only [Int.reduceNeg, ZMod.card, cast_nonneg, Real.sq_sqrt, Complex.sq_abs] at this
  rw [← GaussianInt.intCast_real_norm, Zsqrtd.norm] at this
  norm_cast at this
  simp only [Int.reduceNeg, Int.reduceNegSucc, neg_mul, one_mul, sub_neg_eq_add, ← sq] at this
  exact ⟨_, _, this.symm⟩
