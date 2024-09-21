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

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R]

private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
                      ∑ x ∈ univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show ∀ x y : R, x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ, Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    sum_sdiff_eq_sub (subset_univ _), ← sub_zero (_ - _ + _), add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one, sub_zero, ψ.map_one, χ.map_one, sub_self, mul_zero, zero_mul, add_zero]

end FiniteField

--

section image

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

open Algebra in
private
lemma MulChar.apply_sub_one {n : ℕ} (hn : n ≠ 0) {χ : MulChar F R} {μ : R} (hχ : χ ^ n = 1)
    (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x ≠ 0) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, χ x - 1 = z * (μ - 1) := by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hn hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private
lemma MulChar.apply_sub_one_mul_apply_sub_one {n : ℕ} (hn : n ≠ 0) {χ ψ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ n) (x : F) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.apply_sub_one hn hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ := MulChar.apply_sub_one hn hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, Hz₁ ▸ Hz₂ ▸ by ring⟩

/-
/-- If `χ` is a multiplicative character of order `n` on a finite field `F` with values in
an integral domain `R`, and `μ` is a primitive `n`th root of unity in `R`,
then the Jacobi sum `J(χ,χ)` is in `ℤ[μ] ⊆ R`. -/
lemma jacobiSum_mem_algebraAdjoin {χ : MulChar F R} {μ : R} (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ} := by
  simp_rw [jacobiSum, ← map_mul χ]
  apply Subalgebra.sum_mem
  exact fun _ _ ↦ MulChar.apply_mem_algebraAdjoin hμ _

/-- If `χ` is a multiplicative character satisfying `χ^n = 1` on a finite field `F` with values in
an integral domain `R`, and `μ` is a primitive `n`th root of unity in `R`,
then the Jacobi sum `J(χ,χ)` is in `ℤ[μ] ⊆ R`. -/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq {n : ℕ} (hn : n ≠ 0) {χ : MulChar F R}
    (hχ : χ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ} := by
  simp_rw [jacobiSum, ← map_mul χ]
  apply Subalgebra.sum_mem
  exact fun _ _ ↦ MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hn hχ hμ _
 -/

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` satisfying `χ^n = φ^n = 1`
and with values in an integral domain `R`, and `μ` is a primitive `n`th root of unity in `R`,
then the Jacobi sum `J(χ,φ)` is in `ℤ[μ] ⊆ R`. -/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {χ φ : MulChar F R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ φ ∈ Algebra.adjoin ℤ {μ} :=
  Subalgebra.sum_mem _ fun _ _ ↦ Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hn hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hn hφ hμ _)

/-- If `χ` and `ψ` are multiplicative characters of order dividing `n` on a finite field `F`
with values in an integral domain `R` and `μ` is a primitive `n`th root of unity in `R`,
then `J(χ,ψ) = -1 + z*(μ - 1)^2` for some `z ∈ ℤ[μ] ⊆ R`. (We assume that `#F ≡ 1 mod n`.)
Note that we do not state this as a divisbility in `R`, as this would give a weaker statement. -/
lemma jacobiSum_eq_neg_one_add [DecidableEq F] {n : ℕ} (hn : 2 < n) {χ ψ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hn' : n ∣ Fintype.card F - 1) (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
  obtain ⟨q, hq⟩ := hn'
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq, mul_assoc, ← Hz₁]
    push_cast
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀, jacobiSum_one_nontrivial hψ₀, zero_mul, add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm, hψ₀, jacobiSum_one_nontrivial hχ₀, zero_mul, add_zero]
  · rw [jacobiSum_eq_aux, MulChar.sum_eq_zero_of_ne_one hχ₀, MulChar.sum_eq_zero_of_ne_one hψ₀, hq]
    have H x := MulChar.apply_sub_one_mul_apply_sub_one (by omega) hχ hψ hμ x
    let Z x := Classical.choose <| H x
    have Zdef x := Classical.choose_spec <| H x
    refine ⟨-q * z₁ + ∑ x ∈ univ \ {0, 1}, Z x, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ ↦ (Zdef x).1
    · push_cast
      rw [Hz₁, zero_add, zero_sub]
      conv => enter [1, 2, 2, x]; rw [(Zdef x).2]
      rw [← Finset.sum_mul]
      ring

end image

section GaussSum

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

open MulChar FiniteField

/-- If `χ` is a multiplicative character of order `n` on a finite field `F`,
then `g(χ) * g(χ^(n-1)) = χ(-1)*#F` -/
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ (orderOf χ - 1)) ψ = χ (-1) * Fintype.card F := by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one]
  have H : gaussSum χ⁻¹ ψ = χ (-1) * gaussSum χ⁻¹ ψ⁻¹ := by
    have hχi : χ (-1) = χ⁻¹ (-1) := by
      rw [inv_apply', inv_neg_one]
    rw [AddChar.inv_mulShift, hχi, show (-1 : F) = (-1 : Fˣ) from rfl, gaussSum_mulShift]
  rw [h, H, mul_left_comm, gaussSum_mul_gaussSum_eq_card hχ hψ]

/-- If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`. -/
theorem gaussSum_pow_eq_prod_jacobiSum [DecidableEq F] {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : 2 ≤ orderOf χ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ orderOf χ =
      χ (-1) * Fintype.card F * ∏ i ∈ Icc 1 (orderOf χ - 2), jacobiSum χ (χ ^ i) := by
  -- show `g(χ)^i = g(χ^i) * J(χ,χ)*...*J(χ,χ^(i-1))` for `1 ≤ i < n` by induction
  let n := orderOf χ
  have pow_gauss' : ∀ i ∈ Ico 1 n, (gaussSum χ ψ) ^ i =
      gaussSum (χ ^ i) ψ * ∏ j ∈ Icc 1 (i - 1), jacobiSum χ (χ ^ j) := by
    intro i hi
    rw [mem_Ico] at hi
    obtain ⟨one_le_i, i_lt_n⟩ := hi
    induction i, one_le_i using Nat.le_induction with
    | base =>
        simp only [pow_one, le_refl, tsub_eq_zero_of_le, zero_lt_one, Icc_eq_empty_of_lt,
          prod_empty, mul_one]
    | succ i hi ih =>
        simp only [add_tsub_cancel_right]
        specialize ih <| lt_trans (Nat.lt_succ_self i) i_lt_n
        have gauss_rw : gaussSum (χ ^ i) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ i) * gaussSum (χ ^ (i + 1)) ψ := by
          have chi_pow_i : χ * (χ ^ i) ≠ 1 := by
            rw [← pow_succ']
            exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
          rw [mul_comm, ← jacobiSum_mul_nontrivial chi_pow_i, mul_comm, ← pow_succ']
        apply_fun (· * gaussSum χ ψ) at ih
        rw [mul_assoc, mul_comm (Finset.prod ..) (gaussSum χ ψ), ← pow_succ, ← mul_assoc,
          gauss_rw, mul_comm (jacobiSum ..)] at ih
        rw [ih, mul_assoc, ← Finset.mul_prod_Ico_eq_prod_Icc (b := i)]
        congr
        exact hi
  -- get equality for `i = n-1`
  have gauss_pow_n_sub := pow_gauss' (n - 1) (by simp only [mem_Ico]; omega)
  have hχ₁ : χ ≠ 1 := by
    convert pow_ne_one_of_lt_orderOf (x := χ) one_ne_zero (by omega)
    exact (pow_one χ).symm
  -- multiply again with `g(χ)`
  apply_fun (· * gaussSum χ ψ) at gauss_pow_n_sub
  rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega), mul_right_comm, mul_comm (gaussSum ..),
    gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ] at gauss_pow_n_sub
  convert gauss_pow_n_sub using 1

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
