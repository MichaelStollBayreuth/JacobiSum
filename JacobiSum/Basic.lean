import JacobiSum.AddChar
import JacobiSum.MulChar

open BigOperators  Finset

/-
ABSTRACT: Here, based on chapter 8, section 3 & 4 in 'A Classical Introduction to Modern Number Theory' by K. Ireland and M. Rosen,
          we provide the formalization of the definition as well as some statements about Jacobi sums and the
          necessary preparations.
-/

/-!
### Jacobi sums
-/

section Def

variable {R R' : Type*} [CommRing R] [Fintype R] [DecidableEq R] [CommRing R']

/- The Jacobi sum of two multiplicative characters on a finite commutative ring. -/
def jacobiSum (χ ψ : MulChar R R') : R' :=
  ∑ x : R, (χ x) * (ψ (1 - x))

lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
  simp only [jacobiSum]
  convert sum_eq_sum_one_sub (fun x ↦ χ x * ψ (1 - x)) using 2 with x
  simp only [sub_sub_cancel, mul_comm]

/-- The Jacobi sum is compatible with ring homomorphisms. -/
lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' →+* R'') :
    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

end Def

/-!
### Jacobi sums over finite fields
-/

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R]

/-- The Jacobi sum of two multiplicative characters on a finite field `F` can be written
as a sum over `F \ {0,1}`. -/
lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x ∈ univ \ {0,1}, χ x * ψ (1 - x) := by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, mem_singleton, zero_ne_one,
    not_false_eq_true, sum_insert, isUnit_iff_ne_zero, ne_eq, not_true_eq_false,
    MulCharClass.map_nonunit, sub_zero, map_one, mul_one, sum_singleton, sub_self, mul_zero,
    add_zero]

private
lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
      ∑ x ∈ univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show ∀ x y : R, x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib,
    ← sum_eq_sum_one_sub, Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    sum_sdiff_eq_sub (subset_univ _)]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, mem_singleton, zero_ne_one,
    not_false_eq_true, sum_insert, isUnit_iff_ne_zero, ne_eq, not_true_eq_false,
    MulCharClass.map_nonunit, zero_sub, sub_zero, map_one, sub_self, mul_zero, sum_singleton,
    mul_neg, neg_zero, add_zero]

private
lemma MulChar.val_sub_one [IsDomain R] {n : ℕ} (hn : n ≠ 0) {χ : MulChar F R} {μ : R}
     (hχ : χ ^ n = 1) (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x ≠ 0) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, χ x - 1 = z * (μ - 1) := by
  obtain ⟨k, _, hk⟩ := exists_val_eq_pow hn hχ hμ hx
  obtain ⟨z, hz₁, hz₂⟩ := Algebra.adjoin.sub_one_dvd_pow_sub_one ℤ μ k
  exact ⟨z, hz₁, hk.symm ▸ hz₂⟩

private
lemma MulChar.val_sub_one_mul_val_sub_one [IsDomain R] {n : ℕ} (hn : n ≠ 0) {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ n) (x : F) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    simp only [isUnit_iff_ne_zero, ne_eq, not_true_eq_false, not_false_eq_true,
      MulCharClass.map_nonunit, zero_sub, sub_zero, map_one, sub_self, mul_zero, zero_mul]
  rcases eq_or_ne x 1 with rfl | hx₁
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    simp only [map_one, sub_self, isUnit_iff_ne_zero, ne_eq, not_true_eq_false, not_false_eq_true,
      MulCharClass.map_nonunit, zero_sub, mul_neg, mul_one, neg_zero, zero_mul]
  rw [ne_comm, ← sub_ne_zero] at hx₁
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.val_sub_one hn hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ := MulChar.val_sub_one hn hψ hμ hx₁
  refine ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, ?_⟩
  rw [Hz₁, Hz₂]
  ring

/-- If `χ` is a multiplicative character of order `n` on a finite field `F` with values in
a field `K` of characteristic zero, and `μ` is a primitive `n`th root of unity in `K`,
then the jacobi sum `J(χ,χ)` is in `ℤ[μ] ⊆ K`. -/
lemma jacobiSum_mem_algebraAdjoin {K} [Field K] [CharZero K] {χ : MulChar F K} {μ : K}
    (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    jacobiSum χ χ ∈ (Algebra.adjoin ℤ {μ}) := by
  simp_rw [jacobiSum, ← map_mul χ]
  apply Subalgebra.sum_mem
  exact fun _ _ ↦ MulChar.val_mem_algebraAdjoin hμ _

/-- If `χ` is a multiplicative character satisfying `χ^n = 1` on a finite field `F` with values in
a field `K` of characteristic zero, and `μ` is a primitive `n`th root of unity in `K`,
then the jacobi sum `J(χ,χ)` is in `ℤ[μ] ⊆ K`. -/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq {K} [Field K] [CharZero K] {n : ℕ} (hn : n ≠ 0)
    {χ : MulChar F K} (hχ : χ ^ n = 1) {μ : K} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ χ ∈ (Algebra.adjoin ℤ {μ}) := by
  simp_rw [jacobiSum, ← map_mul χ]
  apply Subalgebra.sum_mem
  exact fun _ _ ↦ MulChar.val_mem_algebraAdjoin_of_pow_eq_one hn hχ hμ _

/-- If `1` is the trivial multiplicative character on a finite field `F`, then `J(1,1) = #F-2`. -/
theorem jacobiSum_triv_triv: (jacobiSum (1 : MulChar F R) 1) = Fintype.card F - 2 := by
  rw [show 1 = MulChar.trivial F R from rfl, jacobiSum_eq_sum_sdiff]
  have : ∀ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intros x hx
    have hx' : IsUnit (x * (1 - x)) := by
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, true_and, ← ne_eq] at hx
      simp only [isUnit_iff_ne_zero]
      exact mul_ne_zero hx.1 <| sub_ne_zero.mpr hx.2.symm
    rw [← map_mul, MulChar.trivial_apply, if_pos hx']
  calc ∑ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ ∈ @univ F _ \ {0, 1}, (1 : R) := sum_congr rfl this
  _ = Finset.card (@univ F _ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff (subset_univ _), card_univ, card_pair zero_ne_one]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card F = 1 + m + 1 :=
      Nat.exists_eq_add_of_lt Fintype.one_lt_card
    rw [show 1 + m + 1 = m + 2 by ring] at hm
    simp only [hm, add_tsub_cancel_right, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right]

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`, then `J(1,χ) = -1`. -/
theorem jacobiSum_triv_nontriv [IsDomain R] {χ : MulChar F R} (hχ : χ.IsNontrivial) :
    jacobiSum 1 χ = -1 := by
  rw [jacobiSum_eq_aux, hχ.sum_eq_zero, MulChar.sum_one_eq_card_units,
    Fintype.card_eq_card_units_add_one (α := F), add_zero, Nat.cast_add, Nat.cast_one,
    ← sub_sub, sub_self, zero_sub, add_right_eq_self]
  calc ∑ x ∈ univ \ {0, 1}, ((MulChar.trivial F R) x - 1) * (χ (1 - x) - 1)
  _ = ∑ x ∈ @univ F _ \ {0, 1}, 0 := by
    refine sum_congr rfl fun x hx ↦ ?_
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simp only [MulChar.trivial_apply, isUnit_iff_ne_zero, ne_eq, hx.1, not_false_eq_true,
      ↓reduceIte, sub_self, zero_mul]
  _ = 0 := sum_const_zero

/-- If `χ` and `ψ` are multiplicative characters of order dividing `n` on a finite field `F`
with values in an integral domain `R` and `μ` is a primitive `n`th root of unity in `R`,
then `J(χ,ψ) = -1 + z*(μ - 1)^2` for some `z ∈ ℤ[μ] ⊆ R`. -/
-- need `Field K` because `X_pow_sub_C_eq_prod` (unnecessarily) requires it
lemma jacobiSum_eq_neg_one_add {K : Type*} [Field K] {n : ℕ} (hn : 2 < n) {χ ψ ρ : MulChar F K}
    {μ : K} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hρ : orderOf ρ = n) (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
  obtain ⟨q, hq⟩ := hρ ▸ ρ.dvd_card_sub_one
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.order_eq_mul hn
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_triv_triv]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq, mul_assoc, ← Hz₁]
    push_cast
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀, jacobiSum_triv_nontriv (ψ.isNontrivial_iff.mpr hψ₀), zero_mul, add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm, hψ₀, jacobiSum_triv_nontriv (χ.isNontrivial_iff.mpr hχ₀), zero_mul,
      add_zero]
  · rw [jacobiSum_eq_aux, (χ.isNontrivial_iff.mpr hχ₀).sum_eq_zero,
      (ψ.isNontrivial_iff.mpr hψ₀).sum_eq_zero, hq]
    let Z x := Classical.choose <| MulChar.val_sub_one_mul_val_sub_one (by omega) hχ hψ hμ x
    have Zdef x : Z x ∈ Algebra.adjoin ℤ {μ} ∧ (χ x - 1) * (ψ (1 - x) - 1) = Z x * (μ - 1) ^ 2 :=
      Classical.choose_spec <| MulChar.val_sub_one_mul_val_sub_one (by omega) hχ hψ hμ x
    refine ⟨-q * z₁ + ∑ x ∈ univ \ {0, 1}, Z x, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ ↦ (Zdef x).1
    · push_cast
      rw [Hz₁, zero_add, zero_sub]
      conv =>
        enter [1, 2, 2, x]
        rw [(Zdef x).2]
      rw [← Finset.sum_mul]
      ring

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`,
then `J(χ,χ⁻¹) = -χ(-1)`. -/
theorem jacobiSum_inv [IsDomain R] {χ : MulChar F R} (hχ : χ.IsNontrivial) :
    jacobiSum χ χ⁻¹ = -(χ (-1)) := by
  rw [jacobiSum]
  simp_rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  -- remove summands = 0
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (1 : F)),
    sub_self, div_zero, χ.map_zero, add_zero]
  have : ∑ x ∈ univ \ {1}, χ (x / (1 - x)) = ∑ x ∈ univ \ {-1}, χ x := by
    refine Finset.sum_bij' (fun (a : F) (_ : a ∈ univ \ {1}) ↦ a / (1 - a))
      (fun (b : F) (_ : b ∈ univ \ {-1}) ↦ b / (1 + b)) (fun x _ ↦ ?_) (fun y hy ↦ ?_)
      (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun x _ ↦ ?_)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and]
      intro hx
      have H : 1 - x ≠ 0 := by
        intro hf
        simp only [hf, div_zero, zero_eq_neg, one_ne_zero] at hx
      field_simp at hx
      rw [eq_comm, ← sub_eq_zero] at hx
      simp only [sub_sub_cancel_left, neg_eq_zero, one_ne_zero] at hx
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and, one_div]
      intro hy
      have H : 1 + y ≠ 0 := by
        intro hf
        simp only [hf, div_zero, zero_ne_one] at hy
      field_simp at hy
    · simp only
      simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm, ← sub_eq_zero] at hx
      field_simp
    · simp only
      simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add] at hy
      field_simp
    · rfl
  rw [this]
  -- insert `χ(-1)` into the sum
  rw [← add_eq_zero_iff_eq_neg, ← Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (-1 : F))]
  -- sum over values of multiplicative character vanishes
  exact hχ.sum_eq_zero

/-- A formula for the product of two Gauss sums. -/
lemma gaussSum_mul (χ φ : MulChar F R) (ψ : AddChar F R) :
    gaussSum χ ψ * gaussSum φ ψ = ∑ t : F, ∑ x : F, χ x * φ (t - x) * ψ t := by
  rw [gaussSum, gaussSum, Finset.sum_mul_sum]
  conv => enter [1, 2, x, 2, x_1]; rw [mul_mul_mul_comm]
  simp only [← ψ.map_add_mul]
  -- variable substitution `x_1 ↦ x_1 - x` in inner sum
  have sum_eq x : ∑ y : F, χ x * φ y * ψ (x + y) = ∑ y : F, χ x * φ (y - x) * ψ y := by
    rw [Finset.sum_bij (fun a _ ↦ a + x)]
    · simp only [mem_univ, forall_true_left, forall_const]
    · simp only [mem_univ, add_left_inj, imp_self, forall_const]
    · intro b _
      use b - x, Finset.mem_univ _
      rw [sub_add_cancel]
    · intro a _
      rw [add_sub_cancel_right, add_comm]
  rw [Finset.sum_congr rfl fun x _ ↦ sum_eq x, Finset.sum_comm]

/-- If `χ` and `ψ` are multiplicative characters on a finite field `F` such that
`χψ` is nontrivial, then `g(χ) * J(χ,ψ) = g(χ) * g(ψ)`. -/
theorem jacobiSum_nontriv_nontriv [IsDomain R] {χ φ : MulChar F R} (h : (χ * φ).IsNontrivial)
    (ψ : AddChar F R) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ := by
  rw [gaussSum_mul _ _ ψ, sum_eq_sum_diff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub, neg_eq_neg_one_mul x, map_mul, mul_left_comm (χ x) (φ (-1)),
      ← MulChar.mul_apply, ψ.map_zero_one, mul_one]
  rw [← mul_sum _ _ (φ (-1)), h.sum_eq_zero, mul_zero, add_zero]
  -- write `x_1 = x*(x_1/x)`
  have sum_eq : ∀ t ∈ univ \ {(0 : F)},
        (∑ x : F, χ x * φ (t - x)) * ψ t =
        (∑ x : F, χ (t * (x / t)) * φ (t - (t * (x / t)))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, ← ne_eq, true_and] at ht
    simp_rw [mul_div_cancel₀ _ ht]
  simp_rw [← sum_mul, sum_congr rfl sum_eq]
  --  set `y := x/t`
  have sum_eq' : ∀ t ∈ univ \ {(0 : F)},
        (∑ x : F, χ (t * (x / t)) * φ (t - (t * (x / t)))) * ψ t =
        (∑ y in univ, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, ← ne_eq, true_and] at ht
    have div_fun_inj : ∀ x ∈ univ, ∀ y ∈ univ, (· / t) x = (· / t) y → x = y :=
      fun _ _ _ _ ↦ (div_left_inj' ht).mp
    have image_eq : Finset.image (· / t) univ = univ := by
      ext a
      simp only [mem_image, mem_univ, true_and, iff_true]
      exact ⟨a * t, mul_div_cancel_right₀ a ht⟩
    conv => enter [2, 1]; rw [← image_eq, sum_image div_fun_inj]
  rw [sum_congr rfl sum_eq']
  simp_rw [← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum]
  conv => enter [2, 2, x]; rw [mul_comm, ← mul_assoc]
  rw [← sum_mul, jacobiSum, gaussSum]
  congr 1
  conv =>
    enter [1]
    rw [sum_eq_sum_diff_singleton_add (mem_univ (0 : F)), MulChar.map_zero, zero_mul, add_zero]
    enter [2, x]
    rw [mul_comm]

/-- If `χ` and `ψ` are multiplicative characters on a finite field `F` with values
in another field and such that `χψ` is nontrivial, then `J(χ,ψ) = g(χ) * g(ψ) / g(χψ)`. -/
theorem jacobiSum_nontriv_nontriv' {R} [Field R] (h : (Fintype.card F : R) ≠ 0) {χ φ : MulChar F R}
    (hχψ : (χ * φ).IsNontrivial) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by
  have : gaussSum (χ * φ) ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial h hχψ hψ
  rw [eq_div_iff this, mul_comm]
  exact jacobiSum_nontriv_nontriv hχψ ψ

section GaussSum

variable [IsDomain R]

open MulChar FiniteField

/-- If `χ` is a multiplicative character of order `n` on a finite field `F`,
then `g(χ) * g(χ^(n-1)) = χ(-1)*#F` -/
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : χ.IsNontrivial) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ (orderOf χ - 1)) ψ = χ (-1) * Fintype.card F := by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    apply_fun (χ * ·) using mul_right_injective χ
    simp only [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one,
      mul_right_inv]
  rw [h]
  have H : gaussSum χ⁻¹ ψ = χ (-1) * gaussSum χ⁻¹ ψ⁻¹ := by
    have hχi : χ (-1) = χ⁻¹ (-1 : Fˣ) := by
      simp only [Units.val_neg, Units.val_one, inv_apply', inv_neg_one]
    rw [AddChar.inv_mulShift, hχi, show (-1 : F) = (-1 : Fˣ) from rfl, gaussSum_mulShift]
  rw [H, mul_left_comm, gaussSum_mul_gaussSum_eq_card hχ hψ]

/-- If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`. -/
theorem gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 ≤ orderOf χ)
    (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ) ^ (orderOf χ) =
      χ (-1) * Fintype.card F * ∏ i in Icc 1 (orderOf χ - 2), jacobiSum χ (χ ^ i) := by
  -- show `g(χ)^i = g(χ^i) * J(χ,χ)*...*J(χ,χ^(i-1))` for `1 ≤ i < n` by induction
  let n := orderOf χ
  have pow_gauss' : ∀ i ∈ Ico 1 n, (gaussSum χ ψ) ^ i =
      gaussSum (χ ^ i) ψ * ∏ j in Icc 1 (i - 1), jacobiSum χ (χ ^ j) := by
    intro i hi
    rw [mem_Ico] at hi
    obtain ⟨one_le_i, i_lt_n⟩ := hi
    induction i, one_le_i using Nat.le_induction with
    | base =>
        simp only [pow_one, ge_iff_le, le_refl, tsub_eq_zero_of_le, gt_iff_lt, zero_lt_one,
          Icc_eq_empty_of_lt, prod_empty, mul_one]
    | succ i hi ih =>
        simp only [add_tsub_cancel_right]
        specialize ih (lt_trans (Nat.lt_succ_self i) i_lt_n)
        have gauss_rw : gaussSum (χ ^ i) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ i) * gaussSum (χ ^ (i + 1)) ψ := by
          have chi_pow_i : (χ * (χ ^ i)).IsNontrivial := by
            rw [← pow_succ']
            refine isNontrivial_pow_of_lt χ _ ?_
            simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, i_lt_n, true_and]
          rw [mul_comm, ← jacobiSum_nontriv_nontriv chi_pow_i, mul_comm, ← pow_succ']
        apply_fun (· * gaussSum χ ψ) at ih
        rw [mul_assoc, mul_comm (Finset.prod ..) (gaussSum χ ψ), ← pow_succ, ← mul_assoc,
          gauss_rw, mul_comm (jacobiSum ..)] at ih
        rw [ih, mul_assoc, ← Finset.mul_prod_Ico_eq_prod_Icc (b := i)]
        congr
        exact hi
  -- get equality for `i = n-1`
  have gauss_pow_n_sub := pow_gauss' (n - 1) (by simp only [mem_Ico]; omega)
  have hχ₁ : χ.IsNontrivial := by
    convert isNontrivial_pow_of_lt χ 1 ?_
    · exact (pow_one χ).symm
    · simp only [mem_Ico, le_refl, true_and]
      omega
  -- multiply again with `g(χ)`
  apply_fun (· * gaussSum χ ψ) at gauss_pow_n_sub
  rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega), mul_right_comm, mul_comm (gaussSum ..),
    gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ] at gauss_pow_n_sub
  convert gauss_pow_n_sub using 1

end GaussSum

/-!
### Gauss and Jacobi sums of characters with values in ℂ
-/

/- Proposition 8.2.2: χ ≠ ε => |g(χ)| = √p -/

/--  The Gauss sum of a multiplicative character on a finite field `F` with values in `ℂ`
has absolute value the square root of `#F`. -/
lemma gaussSum_abs_eq_sqrt {χ : MulChar F ℂ} (hχ : χ.IsNontrivial) {φ : AddChar F ℂ}
    (hφ : φ.IsPrimitive) :
  Complex.abs (gaussSum χ φ) = Real.sqrt (Fintype.card F) := by
  have hF : 0 < ringChar F := Nat.pos_of_ne_zero <| CharP.ringChar_ne_zero_of_finite F
  have gauss_inv : gaussSum χ⁻¹ φ⁻¹ = star (gaussSum χ φ) := by
    rw [← χ.starComp_eq_inv, gaussSum, gaussSum]
    simp only [MulChar.starComp_apply, star_sum, star_mul', RCLike.star_def]
    simp_rw [MulChar.starComp_apply', AddChar.starComp_apply hF]
  have := gaussSum_mul_gaussSum_eq_card hχ hφ
  rw [gauss_inv, Complex.star_def, Complex.mul_conj] at this
  norm_cast at this
  rw [← Real.sqrt_inj (Complex.normSq_nonneg (gaussSum _ _)) (Nat.cast_nonneg _)] at this
  rw [← this]
  rfl

/-- If `χ`, `ψ` and `χψ` are all nontrivial multiplicative characters on a finite field `F`
with values in `ℂ`, then `|J(χ,ψ)| = √#F`. -/
theorem jacobiSum_abs_eq_sqrt {χ φ : MulChar F ℂ} (hχ : χ.IsNontrivial) (hφ : φ.IsNontrivial)
    (hχψ : (χ * φ).IsNontrivial) :
    Complex.abs (jacobiSum χ φ) = Real.sqrt (Fintype.card F) := by
  -- rewrite jacobiSum as gaussSums
  let ψ := FiniteField.primChar F
  have hψ : ψ.IsPrimitive := FiniteField.primChar_isPrimitive F
  have h : (Fintype.card F : ℂ) ≠ 0 := by
    norm_cast
    simp only [Fintype.card_ne_zero, not_false_eq_true]
  rw [jacobiSum_nontriv_nontriv' h hχψ hψ, map_div₀, map_mul]
  -- rewrite each absolute value of a gaussSum as `√#F`
  rw [gaussSum_abs_eq_sqrt hχ hψ, gaussSum_abs_eq_sqrt hφ hψ, gaussSum_abs_eq_sqrt hχψ hψ]
  simp only [Nat.cast_nonneg, Real.mul_self_sqrt, Real.div_sqrt]


/-!
### A proof of Fermat's two-squares theorem via Jacobi sums
-/

open FiniteField MulChar

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
  have h₁ : 1 ∈ Ico 1 (orderOf χ) := by rw [hχ]; norm_num
  have h₂ : 2 ∈ Ico 1 (orderOf χ) := by rw [hχ]; norm_num
  have hχ₁ := isNontrivial_pow_of_lt χ 1 h₁
  rw [pow_one] at hχ₁
  have hχ₂ := isNontrivial_pow_of_lt χ 2 h₂
  rw [pow_two] at hχ₂
  let f : GaussianInt →+* ℂ := GaussianInt.toComplex
  have hJ := jacobiSum_ringHomComp χ χ f
  have hχ₁' := hχ₁.comp GaussianInt.toComplex_injective
  have hχ₂' : (χ.ringHomComp f * χ.ringHomComp f).IsNontrivial := by
    convert hχ₂.comp GaussianInt.toComplex_injective
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