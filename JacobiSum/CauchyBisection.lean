import Mathlib.Analysis.RCLike.Basic

/-!
# Prove a version of Bolzano-Weierstraß using bisection
-/

namespace BolzanoWeierstrass

/-- The sequence `a` has terms in the interval `[x, y]`. -/
def InInterval (a : ℕ → ℝ) (x y : ℝ) : Prop := ∀ n, x ≤ a n ∧ a n ≤ y

/-- The distance between two terms of a bounded sequence is at most the length of the bounding
interval. -/
lemma InInterval.abs_sub_le {a : ℕ → ℝ} {x y : ℝ} (h : InInterval a x y) (m n : ℕ) :
    |a m - a n| ≤ y - x := by
  have hm := h m
  have hn := h n
  grind [abs_le]

/-- The sequence `a` is a Cauchy sequence. -/
def IsCauchy (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m > n, |a m - a n| < ε

/-- A sequence `σ : ℕ → ℕ` is a "subsequence" when it is strictly monotonic. -/
abbrev IsSubsequence (σ : ℕ → ℕ) : Prop := StrictMono σ

/-- A subsequence `σ` satisfies `n ≤ σ n`. -/
lemma IsSubsequence.le {σ : ℕ → ℕ} (h : IsSubsequence σ) (n : ℕ) : n ≤ σ n := by
  induction n with
  | zero => grind
  | succ n ih => specialize h n.lt_add_one; grind

/-- If arbitrary late terms of a sequence have a property `P`, then `P` holds along
a subsequence. -/
lemma exists_subsequence {a : ℕ → ℝ} {P : ℝ → Prop} (h : ∀ N, ∃ n > N, P (a n)) :
    ∃ σ, IsSubsequence σ ∧ ∀ n, P ((a ∘ σ) n) := by
  choose τ hτ using h
  refine ⟨(τ^[· + 1] 0), strictMono_nat_of_lt_succ fun n ↦ ?_, fun n ↦ ?_⟩
  · simpa only [Function.iterate_succ_apply'] using (hτ _).1
  · simpa only [Function.comp_def, Function.iterate_succ_apply'] using (hτ _).2

/-- Bisection lemma: If a sequence takes values in `[x, y]` and `z : ℝ`,
then there is a subsequence in `[x, z]` or a subsequence in `[z, y]`. -/
lemma InInterval.bisection {a : ℕ → ℝ} {x y : ℝ} (ha : InInterval a x y) (z : ℝ) :
    ∃ σ, IsSubsequence σ ∧ (InInterval (a ∘ σ) x z ∨ InInterval (a ∘ σ) z y) := by
  by_cases H : ∀ N, ∃ n > N, a n ≤ z
  · -- infinitely many terms `≤ z`, so the first alternative holds
    obtain ⟨σ, hσs, hσ⟩ := exists_subsequence (P := (· ≤ z)) H
    exact ⟨σ, hσs, .inl fun n ↦ ⟨(ha _).1, hσ n⟩⟩
  · -- only finitely many terms `≤ z`, so the second alternative holds
    push_neg at H
    obtain ⟨N, hN⟩ := H
    refine ⟨(· + (N + 1)), strictMono_id.add_const _, .inr fun n ↦ ⟨?_, (ha _).2⟩⟩
    exact (hN (n + (N + 1)) (by grind)).le

/-- Bundle bounded subsequences into a structure. -/
structure BoundedSubseq (a : ℕ → ℝ) where
  /-- the underlying subsequence -/
  σ : ℕ → ℕ
  /-- lower interval bound -/
  lo : ℝ
  /-- upper interval bound -/
  hi : ℝ
  /-- `σ` is a subsequence -/
  is_subseq : IsSubsequence σ
  /-- all terms of `a ∘ σ` lie in the interval `[lo, hi]` -/
  is_bdd : InInterval (a ∘ σ) lo hi

namespace BoundedSubseq

/-- The bisection subsequence using the midpoint bundled as a `BoundedSubseq a`. -/
noncomputable
def bisection {a : ℕ → ℝ} (α : BoundedSubseq a) : BoundedSubseq a := by
  classical
  choose τ hτ H using α.is_bdd.bisection ((α.lo + α.hi) / 2)
  exact if HH : InInterval (a ∘ α.σ ∘ τ) α.lo ((α.lo + α.hi) / 2)
    then ⟨α.σ ∘ τ, α.lo, (α.lo + α.hi) / 2, α.is_subseq.comp hτ, HH⟩
    else ⟨α.σ ∘ τ, (α.lo + α.hi) / 2, α.hi, α.is_subseq.comp hτ, H.resolve_left HH⟩

/-- Record the fact that the subsequence in `bisection_boundedSubseq α` is obtained
from `α.σ` by composing with a subsequence. -/
lemma exists_subseq_bisection {a : ℕ → ℝ} (α : BoundedSubseq a) :
    ∃ τ, IsSubsequence τ ∧ α.bisection.σ = α.σ ∘ τ := by
  simp only [bisection]
  refine ⟨?_, ?_, ?_⟩
  case refine_3 => split_ifs <;> simp only <;> congr <;> rfl
  case refine_2 => exact Classical.choose_spec (α.is_bdd.bisection ((α.lo + α.hi) / 2)) |>.1

/-- The main property: the bisection subsequence lies in an interval of half the
original interval width. -/
lemma bisection_width_eq {a : ℕ → ℝ} (α : BoundedSubseq a) :
    α.bisection.hi - α.bisection.lo = (α.hi - α.lo) / 2 := by
  grind [bisection]

/-- The terms of `(bisection_boundedSubseq α).σ` are also terms of `α.σ`. -/
lemma bisection_subseq {a : ℕ → ℝ} (α : BoundedSubseq a) (k : ℕ) :
    ∃ l, α.bisection.σ k = α.σ l := by
  obtain ⟨τ, _, h⟩ := α.exists_subseq_bisection
  refine ⟨τ k, ?_⟩
  rw [h, Function.comp_apply]

/-- Iterate the bisection construction to obtain a sequence of nested subsequences. -/
noncomputable
def iterate_bisection {a : ℕ → ℝ} (α : BoundedSubseq a) : ℕ → BoundedSubseq a
| 0 => α
| n + 1 => (iterate_bisection α n).bisection

/-- The `n`th subsequence lies in a small interval- -/
lemma iterate_bisection_width_eq {a : ℕ → ℝ} (α : BoundedSubseq a) (n : ℕ) :
    (α.iterate_bisection n).hi - (α.iterate_bisection n).lo = (α.hi - α.lo) / 2 ^n := by
  induction n with
  | zero => grind [iterate_bisection]
  | succ n ih =>
    simp only [iterate_bisection]
    convert bisection_width_eq _ using 1
    grind

/-- The extracted diagonal sequence is a subsequence. -/
lemma diagonal_subsequence {a : ℕ → ℝ} (α : BoundedSubseq a) :
    IsSubsequence fun n ↦ (iterate_bisection α n).σ n := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  simp only [iterate_bisection]
  obtain ⟨τ, hτ, hτ'⟩ := (iterate_bisection α n).exists_subseq_bisection
  rw [hτ', Function.comp_apply]
  exact (iterate_bisection α n).is_subseq <| (hτ.le n).trans_lt <| hτ n.lt_add_one

/-- The `n`th iterated subsequence is a subsequence of the `m`th iterated subsequence
when `m ≤ n`. -/
lemma subseq_in_iterate {a : ℕ → ℝ} (α : BoundedSubseq a) {m n : ℕ} (hmn : m ≤ n)
    (k : ℕ) :
    ∃ l, (iterate_bisection α n).σ k = (iterate_bisection α m).σ l := by
  induction n, hmn using Nat.le_induction generalizing k with
  | base => exact ⟨k, rfl⟩
  | succ n hmn ih =>
    simp only [iterate_bisection]
    obtain ⟨l', hl'⟩ := (iterate_bisection α n).bisection_subseq k
    obtain ⟨l, hl⟩ := ih l'
    grind

end BoundedSubseq

open BoundedSubseq

/-- A version of the **Bolzano-Weierstraß Theorem**:

A bounded sequence has a Cauchy subsequence. -/
theorem exists_isSubsequence_and_isCauchy_of_inInterval {a : ℕ → ℝ} {x y : ℝ}
    (ha : InInterval a x y) :
    ∃ σ, IsSubsequence σ ∧ IsCauchy (a ∘ σ) := by
  have hxy : x ≤ y := (ha 0).1.trans (ha 0).2
  -- turn `a` into the obvious bounded subsequence of itself
  let α : BoundedSubseq a := ⟨id, x, y, strictMono_id, ha⟩
  -- take the diagonal subsequence obtained from the iterative bisection construction
  refine ⟨fun n ↦ (iterate_bisection α n).σ n, diagonal_subsequence _, fun ε hε ↦ ?_⟩
  -- we need to show the Cauchy property
  -- find `N` large enough so that the `N`th interval has width `< ε`
  obtain ⟨N, hN⟩ : ∃ N, (y - x) / 2 ^ N < ε := by
    have (N : ℕ) : 0 < (2 : ℝ) ^ N := mod_cast N.two_pow_pos
    simp_rw [div_lt_iff₀ <| this _, ← div_lt_iff₀' hε]
    exact pow_unbounded_of_one_lt ((y - x) / ε) one_lt_two
  -- take this `N`
  refine ⟨N, fun n hn m hmn ↦ ?_⟩
  simp only [Function.comp_apply]
  -- write both terms as terms in the `n`th subsequence
  obtain ⟨l, hl⟩ := α.subseq_in_iterate hmn.le m
  rw [hl]; clear hl hmn m
  -- now we can apply the distance bound from being in an interval
  have := (iterate_bisection α n).is_bdd.abs_sub_le l n
  simp only [Function.comp_apply] at this
  grw [this]; clear this
  -- it remains to verify that the interval width is sufficiently small
  rw [α.iterate_bisection_width_eq n, show α.hi = y from rfl, show α.lo = x from rfl]
  suffices (y - x) / 2 ^ n ≤ (y - x) / 2 ^ N by grind
  gcongr <;> grind

end BolzanoWeierstrass
