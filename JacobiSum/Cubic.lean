import JacobiSum.Basic

open Finset

namespace JacobiSumCubic

-- `R` is an integral domain with a primitive cube root of unity `ω`.
variable {R : Type*} [CommRing R] [IsDomain R] {ω : R}

lemma rel_of_IsPrimitiveRoot (hω : IsPrimitiveRoot ω 3) : ω ^ 2 + ω + 1 = 0 := by
  rw [← hω.geom_sum_eq_zero (by omega)]
  simp only [sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]
  abel

/-- If `ω` is a primitive cube root of unity, then any element of `ℤ[ω] ⊆ R` has the form
`a + b*ω` with integers `a` and `b`. -/
lemma integral_repr (hω : IsPrimitiveRoot ω 3) {x : R} (hx : x ∈ Algebra.adjoin ℤ {ω}) :
    ∃ a b : ℤ, x = a + b * ω := by
  have : Polynomial.aeval ω (Polynomial.cyclotomic 3 ℤ) = 0 := by
    simp only [Polynomial.cyclotomic_three, map_add, map_pow, Polynomial.aeval_X, map_one,
      rel_of_IsPrimitiveRoot hω]
  change x ∈ Subalgebra.toSubmodule (Algebra.adjoin ℤ {ω}) at hx
  rw [← Submodule.span_range_natDegree_eq_adjoin (Polynomial.cyclotomic.monic 3 ℤ) this,
    Polynomial.natDegree_cyclotomic, show range (Nat.totient 3) = {0, 1} from rfl] at hx
  simp only [image_insert, pow_zero, image_singleton, pow_one, coe_insert, coe_singleton] at hx
  obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.1 hx
  exact ⟨a, b, hx ▸ by simp only [zsmul_eq_mul, mul_one]⟩

end JacobiSumCubic


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open MulChar BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] in
/-- If `χ` is a cubic multiplicative character on a finite field `F`,
then `g(χ)³ = #F * J(χ,χ)`. -/
theorem gaussSum_pow_three {χ : MulChar F R} (hχ : orderOf χ = 3) {ψ : AddChar F R}
    (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ) ^ 3 = Fintype.card F * jacobiSum χ χ := by
  simpa only [hχ, val_neg_one_eq_one_of_odd_order ⟨1, rfl⟩ (hχ ▸ pow_orderOf_eq_one χ), one_mul,
    Nat.succ_sub_succ_eq_sub, tsub_zero, Icc_self, prod_singleton, pow_one]
    using gaussSum_pow_eq_prod_jacobiSum (by omega : 2 ≤ orderOf χ) hψ

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If `χ` is a cubic multiplicative character on a finite field `F` with values in an
intgral domain `R` and `ω` is a primitive cube root of unity in `R`,
then `J(χ,χ)= -1 + 3*z` with `z ∈ ℤ[ω] ⊆ R`. -/
lemma jacobiSum_eq_neg_one_add_three_mul_of_orderOf_eq_three {χ : MulChar F R} (hχ : orderOf χ = 3)
    {ω : R} (hω : IsPrimitiveRoot ω 3) :
    ∃ z ∈ Algebra.adjoin ℤ {ω}, jacobiSum χ χ = -1 + 3 * z := by
  have hχ' : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  obtain ⟨z, hz, Hz⟩ := jacobiSum_eq_neg_one_add (by omega) hχ' hχ' hχ hω
  have hω' : (ω - 1) ^ 2 = 3 * (-ω) := by
    linear_combination JacobiSumCubic.rel_of_IsPrimitiveRoot hω
  rw [hω', mul_comm, mul_assoc] at Hz
  refine ⟨-ω * z, ?_, Hz⟩
  exact Subalgebra.mul_mem _ (Subalgebra.neg_mem _ <| Algebra.self_mem_adjoin_singleton ℤ ω) hz

/-- If `χ` is a cubic multiplicative character on a finite field `F` with values
in an integral domain `R` and `ω` is a primitive cube root of unity in `R`,
then `J(χ,χ)= (-1 + 3*a) + 3*b*ω` with integers `a` and `b`. -/
lemma jacobiSum_eq_neg_one_add_three_mul_add_of_orderOf_eq_three {χ : MulChar F R}
    (hχ : orderOf χ = 3) {ω : R} (hω : IsPrimitiveRoot ω 3) :
    ∃ a b : ℤ, jacobiSum χ χ = -1 + 3 * a + 3 * b * ω := by
  obtain ⟨z, hz, Hz⟩ := jacobiSum_eq_neg_one_add_three_mul_of_orderOf_eq_three hχ hω
  obtain ⟨a, b, hab⟩ := JacobiSumCubic.integral_repr hω hz
  rw [hab, mul_add, ← add_assoc, ← mul_assoc] at Hz
  exact ⟨a, b, Hz⟩
