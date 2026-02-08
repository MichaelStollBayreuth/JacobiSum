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

lemma natDegree_scale {c : R} (hc : c ≠ 0) : (aeval (c • (X : R[X])) p).natDegree = p.natDegree := by
  refine map_natDegree_eq_natDegree p fun n a ha ↦ ?_
  simp only [aeval_monomial, algebraMap_eq, natDegree_C_mul ha]
  compute_degree
  exact pow_ne_zero n hc

omit [NoZeroDivisors R] in
lemma coeff_aeval_C_mul_X (c : R) (n : ℕ) : (aeval (C c * X) p).coeff n = c ^ n * p.coeff n := by
  simp [aeval_eq_sum_range, finset_sum_coeff, mul_pow]
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


#exit
/-- A missing API lemma for `PartENat.find`. -/
lemma PartENat.find_eq_natFind {P : Nat → Prop} [DecidablePred P] (h : ∃ n, P n) :
    PartENat.find P = Nat.find h := by
  apply Part.ext'
  · simp only [find_dom _ h, dom_natCast]
  · simp only [dom_natCast, find_get, get_natCast', imp_self, implies_true]


namespace Nat

/-- Helper function for `Nat.findWithBound`. -/
@[simp]
def findWithBound_aux (P : Nat → Prop) [DecidablePred P] (n : Nat) : Nat → Nat
| 0 => n
| k + 1 => if P n then n else findWithBound_aux P (n + 1) k

/-- The defining property of `Nat.findWithBound_aux`. -/
lemma findWithBound_aux_spec (P : Nat → Prop) [DecidablePred P] (n k m : Nat) :
    findWithBound_aux P n k = m ↔
      n ≤ m ∧ m ≤ k + n  ∧ (∀ l, n ≤ l → l < m → ¬ P l) ∧ (P m ∨ m = k + n) := by
  induction k generalizing n with
  | zero =>
      simp only [findWithBound_aux, zero_add]
      refine ⟨fun H ↦ ?_, fun ⟨H₁, H₂, _⟩ ↦ le_antisymm H₁ H₂⟩
      simpa only [H, le_refl, zero_add, or_true, and_true, true_and]
        using fun _ hl₁ hl₂ _ ↦ (hl₂.trans_le hl₁).false
  | succ k ih =>
      simp only [findWithBound_aux]
      by_cases hP : P n <;> simp only [hP, ↓reduceIte]
      · refine ⟨fun H ↦ ?_, fun ⟨H₁, _, H₃, _⟩ ↦ ?_⟩
        · simpa only [H, le_refl, le_add_iff_nonneg_left, _root_.zero_le, self_eq_add_left,
            add_eq_zero, one_ne_zero, and_false, or_false, true_and]
            using ⟨fun _ hl₁ hl₂ _ ↦ (hl₂.trans_le hl₁).false, H ▸ hP⟩
        · exact le_antisymm H₁ <| le_of_not_lt <| (imp_not_comm.mp <| H₃ n le_rfl) hP
      · specialize ih (n + 1)
        rw [show k + (n + 1) = k + 1 + n by rw [add_comm n, add_assoc]] at ih
        refine ⟨fun H ↦ ?_, fun ⟨H₁, H₂, H₃, H₄⟩ ↦ ?_⟩
        · obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih.mp H
          refine ⟨(le_add_right n 1).trans ih₁, ih₂, fun l hl₁ hl₂ ↦ ?_, ih₄⟩
          exact (le_iff_lt_or_eq.mp hl₁).elim (fun h ↦ ih₃ l h hl₂) fun h ↦ h ▸ hP
        · have H : n ≠ m := by
            rintro rfl
            exact (zero_ne_add_one k).symm <| self_eq_add_left.mp <| H₄.resolve_left hP
          exact ih.mpr ⟨lt_of_le_of_ne H₁ H, H₂, fun l h ↦ H₃ l ((le_add_right n 1).trans h), H₄⟩


/-- `Nat.findWithBound P n` returns the smallest `m ≤ n` such that `P m` holds if such an `m`
exists; otherwise, `Nat.findWithBound P n = n`. -/
def findWithBound (P : Nat → Prop) [DecidablePred P] (n : Nat) : Nat :=
  findWithBound_aux P 0 n

/-- The defining property of `Nat.findWithBound`. -/
lemma findWithBound_eq_iff (P : Nat → Prop) [DecidablePred P] (n m : ℕ) :
    findWithBound P n = m ↔ m ≤ n ∧ (∀ k < m, ¬ P k) ∧ (P m ∨ m = n) := by
  simpa only [_root_.zero_le, add_zero, true_implies, true_and] using findWithBound_aux_spec P 0 ..

lemma findWithBound_spec (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    P (findWithBound P n) ∨ findWithBound P n = n :=
  ((findWithBound_eq_iff P n _).mp rfl).2.2

lemma findWithBound_le' (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    findWithBound P n ≤ n :=
  ((findWithBound_eq_iff P n _).mp rfl).1

lemma findWithBound_le {P : Nat → Prop} [DecidablePred P] (n : Nat) {m : Nat} (h : P m) :
    findWithBound P n ≤ m :=
  le_of_not_lt <| (imp_not_comm.mp <| ((findWithBound_eq_iff P n _).mp rfl).2.1 m) h

lemma findWithBound_min {P : Nat → Prop} [DecidablePred P] {n m : Nat}
    (hm : m < findWithBound P n) :
    ¬P m :=
  ((findWithBound_eq_iff P n _).mp rfl).2.1 m hm

/-- `Nat.findWithBound P n` agrees with `Nat.find (_ : ∃ m, P m)` if `P m` holds
for some `m ≤ n`. -/
lemma findWithBound_eq_find_of_witness {P : Nat → Prop} [DecidablePred P] {m n : Nat} (h : m ≤ n)
    (hP : P m) :
    findWithBound P n = Nat.find ⟨m, hP⟩ := by
  rw [findWithBound_eq_iff]
  refine ⟨(find_le_iff ⟨m, hP⟩ n).mpr ⟨m, h, hP⟩, ?_, .inl <| Nat.find_spec ⟨m, hP⟩⟩
  exact fun k hk ↦ (lt_find_iff ⟨m, hP⟩ k).mp hk k le_rfl

/-- A constructive version of `multiplicity` for natural numbers. -/
def multiplicity' (m n : Nat) : PartENat :=
  if n = 0 ∨ m = 1 then ⊤ else findWithBound (fun k ↦ ¬ m ^ (k + 1) ∣ n) n

/-- `Nat.multiplicity' m n` agrees with `multiplicity m n` for `m n : Nat`. -/
lemma multiplicity'_eq_multiplicity (m n : Nat) : multiplicity' m n = multiplicity m n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [multiplicity', true_or, ↓reduceIte, multiplicity.zero]
  rcases eq_or_ne m 1 with rfl | hm
  · simp only [multiplicity', or_true, ↓reduceIte, isUnit_one, multiplicity.isUnit_left]
  simp only [multiplicity', hn, hm, or_self, ↓reduceIte]
  have key : ¬ m ^ (n + 1) ∣ n := by
    intro H
    rcases eq_or_ne m 0 with rfl | hm₀
    · exact hn <| zero_dvd_iff.mp <| (zero_pow (M₀ := Nat) <| succ_ne_zero n) ▸ H
    · exact lt_irrefl n <|
        calc n
          _ < n + 1 := lt_add_one n
          _ < m ^ (n + 1) := lt_pow_self (by omega) _
          _ ≤ n := le_of_dvd (zero_lt_of_ne_zero hn) H
  rw [findWithBound_eq_find_of_witness le_rfl key]
  exact (PartENat.find_eq_natFind ⟨_, key⟩).symm

count_heartbeats in -- 272
example : multiplicity 5 10485760000000000000000000 = 19 := by
  rw [← multiplicity'_eq_multiplicity]
  rfl
