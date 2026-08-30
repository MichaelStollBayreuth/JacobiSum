import Mathlib

/-!
# A proof of the fundamental theorem of algebra

Following Argand.
-/

section aux

namespace Polynomial

variable {R : Type*} [CommSemiring R]

lemma eval_aeval (a : R) (p q : R[X]) :
    eval a (aeval q p) = eval (eval a q) p := by
  rw [← eval_comp, comp_eq_aeval]

variable [NoZeroDivisors R] (p : R[X])

lemma natDegree_shift (a : R) : (aeval (X + C a : R[X]) p).natDegree = p.natDegree := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [natDegree_of_subsingleton]
  · refine map_natDegree_eq_natDegree p fun n c hc ↦ ?_
    simp [natDegree_C_mul hc]

lemma natDegree_scale {c : R} (hc : c ≠ 0) :
    (aeval (c • (X : R[X])) p).natDegree = p.natDegree := by
  refine map_natDegree_eq_natDegree p fun n a ha ↦ ?_
  simp only [aeval_monomial, algebraMap_eq, natDegree_C_mul ha]
  compute_degree
  exact pow_ne_zero n hc

omit [NoZeroDivisors R] in
lemma coeff_aeval_C_mul_X (c : R) (n : ℕ) : (aeval (C c * X) p).coeff n = c ^ n * p.coeff n := by
  simp [aeval_eq_sum_range, mul_pow]
  conv => enter [1, 2, i]; rw [← C_pow, coeff_C_mul_X_pow]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  split
  · rw [mul_comm]
  · have : n > p.natDegree := by omega
    simp [coeff_eq_zero_of_natDegree_lt this]

lemma coeff_X_pow_mul_of_lt {k n : ℕ} (h : n < k) : (X ^ k * p).coeff n = 0 := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine coeff_eq_zero_of_lt_natTrailingDegree ?_
  rw [natTrailingDegree_mul (pow_ne_zero k X_ne_zero) hp, natTrailingDegree_X_pow]
  omega

end Polynomial

end aux

namespace FTA

lemma aux {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    ‖1 - x * (1 + z)‖ < 1 := by
  rw [mul_add, ← sub_sub, mul_one]
  calc ‖1 - x - x * z‖
    _ ≤ ‖(1 - x : ℂ)‖ + ‖x * z‖ := norm_sub_le ..
    _ = 1 - x + x * ‖z‖ := by
      rw [norm_mul]
      norm_cast
      rw [Real.norm_of_nonneg hx.le, Real.norm_of_nonneg (by linarith)]
    _ < 1 - x + x * (1 / 2) := by gcongr
    _ = 1 - x / 2 := by ring
    _ < 1 := by linarith

open Polynomial

-- We work with a non-constant polynomial `f` with complex coefficients.
variable {f : ℂ[X]} (hf : 0 < f.natDegree)

lemma smaller_value_aux₁ (g : ℂ[X]) (k : ℕ) (h : f = 1 - X ^ (k + 1) * (1 + X * g)) :
    ∃ z, ‖eval z f‖ < 1 := by
  obtain ⟨ε, hε, hg⟩ : ∃ ε > (0 : ℝ), ∀ z, ‖z‖ < ε → ‖eval z (X * g)‖ < 1 / 2 := by
    have := (X * g).continuous
    rw [Metric.continuous_iff] at this
    obtain ⟨ε, hε, h⟩ := this 0 _ one_half_pos
    simp only [dist_eq_norm, sub_zero, eval_mul, eval_X, zero_mul, Complex.norm_mul] at h
    simp only [eval_mul, eval_X, Complex.norm_mul]
    exact ⟨ε, hε, h⟩
  rw [h]
  let δ : ℝ := min (ε / 2) (1 / 2)
  refine ⟨δ, ?_⟩
  have hδ : ‖(δ : ℂ)‖ < ε := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ δ)]
    linarith [min_le_left (ε / 2) (1 / 2)]
  specialize hg δ hδ
  simp only [eval_mul, eval_X] at hg
  simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X, eval_add]
  rw [show (δ : ℂ) ^ (k + 1) = (δ ^ (k + 1) :) by norm_cast]
  have hεk : 0 < δ ^ (k + 1) := by positivity
  refine aux hεk ?_ hg
  have hδ₂ : δ ≤ 1 / 2 := min_le_right (ε / 2) (1 / 2)
  calc
  δ ^ (k + 1) ≤ δ := pow_le_of_le_one (by positivity) (by linarith) k.zero_ne_add_one.symm
  _ < 1 := by linarith

include hf

-- attribute [-simp] smul_X -- to speed up `simp?`

lemma poly_aux (h : eval 0 f ≠ 0) : ∃ (c c' : ℂ) (k : ℕ) (g : ℂ[X]),
    aeval (c • X) (c' • f) = 1 - X ^ (k + 1) * (1 + X * g) ∧ c ≠ 0 ∧ c' ≠ 0 := by
  have H : ∃ k : ℕ, f.coeff (k + 1) ≠ 0 := by
    refine ⟨f.natDegree - 1, ?_⟩
    simp only [Nat.sub_add_cancel hf, coeff_natDegree, ne_eq, leadingCoeff_eq_zero]
    exact ne_zero_of_natDegree_gt hf
  let k : ℕ := Nat.find H
  have hk : f.coeff (k + 1) ≠ 0 := Nat.find_spec H
  let c' : ℂ := (eval 0 f)⁻¹
  have hc' : c' ≠ 0 := inv_ne_zero h
  let c : ℂ := (-(f.coeff (k + 1))⁻¹ * (eval 0 f)) ^ (1 / (k + 1) : ℂ)
  have hc : c ≠ 0 := by
    refine (Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_).mpr ?_
    · apply one_div_ne_zero
      norm_cast
    · simp [h, hk]
  let g : ℂ[X] := ofFn (f.natDegree - (k + 1)) fun i ↦ - c' * f.coeff (k + 2 + i) * c ^ (k + 2 + i)
  have hg {n : ℕ} : g.coeff n = -c' * f.coeff (k + 2 + n) * c ^ (k + 2 + n) := by
    rcases lt_or_ge n (f.natDegree - (k + 1)) with hn | hn
    · simp [g, hn]
    · rw [coeff_eq_zero_of_natDegree_lt (p := f) (by omega)]
      simp [g, hn]
  refine ⟨c, c', k, g, ext fun n ↦ ?_, hc, hc'⟩
  simp only [smul_eq_C_mul, map_mul, aeval_C, algebraMap_eq, coeff_C_mul, coeff_aeval_C_mul_X,
    coeff_sub]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [field, c', coeff_zero_eq_eval_zero]
  -- now `n > 0`
  simp only [coeff_one, hn.ne', ↓reduceIte, zero_sub, c']
  rcases le_or_gt n k with hnk | hnk
  · -- `n ≤ k`
    rw [coeff_X_pow_mul_of_lt _ (by omega)]
    simpa [Nat.sub_add_cancel hn, h, hc] using Nat.find_min H (show n - 1 < k by omega)
  · -- `n > k`
    rcases eq_or_ne n (k + 1) with rfl | hnk'
    · have := coeff_X_pow_mul (1 + X * g) (k + 1) 0
      rw [zero_add] at this
      simp only [neg_mul, one_div, this, coeff_add, coeff_one_zero, mul_coeff_zero, coeff_X_zero,
        zero_mul, add_zero, c]
      rw [← Nat.cast_succ, Complex.cpow_nat_inv_pow _ (by omega)]
      field_simp
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show k + 2 ≤ n by omega)
      rw [show k + 2 + l = l + 1 + (k + 1) by omega, coeff_X_pow_mul, mul_comm (c ^ _),
        show l + 1 + (k + 1) = k + 2 + l by omega]
      simp [hg, c', mul_assoc, coeff_one]

lemma smaller_value {z₀ : ℂ} (h : eval z₀ f ≠ 0) : ∃ z, ‖eval z f‖ < ‖eval z₀ f‖ := by
  let f₁ : ℂ[X] := aeval (X + C z₀) f
  have hf₁ : 0 < f₁.natDegree := by rwa [natDegree_shift]
  have hf₀ : eval 0 f₁ ≠ 0 := by simp [f₁, eval_aeval, h]
  obtain ⟨c, c', k, g, h', hc, hc'⟩ := poly_aux hf₁ hf₀
  let f₂ : ℂ[X] := aeval (c • X) (c' • f₁)
  obtain ⟨z, hz⟩ := smaller_value_aux₁ g k h'
  have hc'₁ : c' = (eval z₀ f)⁻¹ := by
    apply_fun (eval 0 ·) at h'
    simp only [eval_aeval, eval_smul, eval_X, smul_eq_mul, mul_zero, eval_add, eval_C, zero_add,
      pow_succ, eval_sub, eval_one, eval_mul, eval_pow, zero_mul, add_zero, sub_zero, f₁] at h'
    exact eq_inv_of_mul_eq_one_left h'
  use c * z + z₀
  have H : eval z f₂ = (eval z₀ f)⁻¹ * eval (c * z + z₀) f := by
    simp [f₂, f₁, smul_eq_C_mul, hc'₁, eval_aeval]
  rwa [H, norm_mul, norm_inv, inv_mul_lt_one₀ <| norm_pos_iff.mpr h] at hz

theorem fundamental_thm : ∃ z₀, eval z₀ f = 0 := by
  obtain ⟨z₀, h⟩ := exists_forall_norm_le f
  contrapose! h
  exact smaller_value hf (h z₀)
