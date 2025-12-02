import Mathlib

/-!
# Prove the Conditional Convergence Theorem
-/

/-!
### Auxiliary results
-/

namespace ConditionalConvergence

open Finset in
/-- If `e` is a bijection between `ℕ ⊕ ℕ` and `ℕ`, then it takes on large values
on sufficiently large inputs. -/
lemma eventually_le (e : ℕ ⊕ ℕ ≃ ℕ) (N : ℕ) :
    ∃ n, ∀ m ≥ n, N ≤ e (.inl m) ∧ N ≤ e (.inr m) := by
  let s := preimage (range N) e e.injective.injOn
  have hs p : p ∈ s ↔ ∃ l < N, e p = l := by simp [s]
  let t₁ := preimage s Sum.inl Sum.inl_injective.injOn
  have ht₁ k : k ∈ t₁ ↔ .inl k ∈ s := by simp [t₁]
  let t₂ := preimage s Sum.inr Sum.inr_injective.injOn
  have ht₂ k : k ∈ t₂ ↔ .inr k ∈ s := by simp [t₂]
  refine ⟨1 + max (sup t₁ id) (sup t₂ id), fun m hm ↦ ⟨?_, ?_⟩⟩
  · have : m ∉ t₁ := by grind [le_sup]
    grind
  · have : m ∉ t₂ := by grind [le_sup]
    grind

/-!
### Interlacing constructions

We define a structure `Interlace` that captures the essence of the two relevant constructions:
* separating the original sequence into its nonnegative and negative parts;
* interleaving these to form a new sequence.

We then provide some API lemmas for it.
-/

/-- A structure capturing the interlacing behavior of the constructions -/
@[grind]
structure Interlace (α : Type*) where
  /-- An `α`-valued sequence -/
  s : ℕ → α
  /-- The first index function -/
  i : ℕ → ℕ
  /-- At zero, `i` is zero. -/
  hi : i 0 = 0 := by grind
  /-- The second index function -/
  j : ℕ → ℕ
  /-- At zero, `j` is zero. -/
  hj : j 0 = 0 := by grind
  /-- The predicate that decides which index to increment -/
  P : ℕ → α → Prop
  /-- If `P n (s n)` holds, then `i` is incremented. -/
  Hi n : P n (s n) → i (n + 1) = i n + 1 ∧ j (n + 1) = j n := by grind
  /-- If `P n (s n)` does not hold, then `j` is incremented. -/
  Hj n : ¬P n (s n) → i (n + 1) = i n ∧ j (n + 1) = j n + 1 := by grind

namespace Interlace

open Finset

variable {α : Type*}

/-- The predicate that decides which index to increment. -/
abbrev pred (I : Interlace α) (n : ℕ) : Prop :=
  I.P n (I.s n)

noncomputable local instance (I : Interlace α) : DecidablePred I.pred :=
  Classical.decPred _

/-- The "mirror" of an `Interlace` structure: we swap `i` and `j` and replace `P` by `¬P`. -/
def mirror (I : Interlace α) : Interlace α where
  s := I.s
  i := I.j
  hi := I.hj
  j := I.i
  hj := I.hi
  P n st := ¬ I.P n st
  Hi n h := by have := I.Hj n h; grind
  Hj n h := by have := I.Hi n <| Classical.not_not.mp h; grind

/-- The map `ℕ → ℕ ⊕ ℕ` defined by an `Interlace` structure. -/
@[grind]
noncomputable def e (I : Interlace α) (n : ℕ) : ℕ ⊕ ℕ :=
  if I.pred n then .inl <| I.i n else .inr <| I.j n

lemma mono_i (I : Interlace α) : Monotone I.i := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  have := I.Hi n
  have := I.Hj n
  by_cases I.pred n <;> grind

lemma mono_j (I : Interlace α) : Monotone I.j :=
  mono_i I.mirror

lemma i_const_of_not_pred {I : Interlace α} {m n : ℕ} (h : ∀ k ∈ Ico m n, ¬ I.pred k) :
    ∀ k ∈ Icc m n, I.i k = I.i m := by
  intro k hk
  obtain ⟨hk₁, hk₂⟩ := mem_Ico.mp hk
  induction k, hk₁ using Nat.le_induction with
  | base => rfl
  | succ k hk' ih =>
    rw [← ih (by grind) (by grind)]
    exact (I.Hj k (h k (by grind))).1

/-- The `i` function is surjective if the predicate `I.pred` holds frequently. -/
lemma surjective_i {I : Interlace α} (freqP : ∀ n, ∃ m ≥ n, I.pred m) :
    Function.Surjective I.i := by
  intro n
  induction n with
  | zero => exact ⟨0, I.hi⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    have H := @Nat.find_min _ _ (freqP m)
    set N := Nat.find (freqP m)
    use N + 1
    replace H : I.i N = n := hm ▸ i_const_of_not_pred (n := N) (by grind) N (by grind)
    exact H ▸ (I.Hi N (Nat.find_spec (freqP m)).2).1

/-- The `j` function is surjective if the predicate `¬I.pred` holds frequently. -/
lemma surjective_j {I : Interlace α} (freqnP : ∀ n, ∃ m ≥ n, ¬ I.pred m) :
    Function.Surjective I.j :=
  surjective_i (I := I.mirror) freqnP

lemma surjective_i' {I : Interlace α} (freqP : ∀ n, ∃ m ≥ n, I.pred m) (i : ℕ) :
    ∃ n, I.i n = i ∧ I.pred n := by
  obtain ⟨n, hn⟩ := surjective_i freqP i
  have H := @Nat.find_min _ _ (freqP n)
  push_neg at H
  set N := Nat.find (freqP n)
  refine ⟨N, ?_, (Nat.find_spec (freqP n)).2⟩
  exact hn ▸ i_const_of_not_pred (n := N) (by grind) N (by grind)

lemma surjective_j' {I : Interlace α} (freqnP : ∀ n, ∃ m ≥ n, ¬ I.pred m) (j : ℕ) :
    ∃ n, I.j n = j ∧ ¬ I.pred n :=
  surjective_i' (I := I.mirror) freqnP j

/-- The equivalence `ℕ ≃ ℕ ⊕ ℕ` extracted from an `Interlace` structure `I` when both `I.pred`
and `¬I.pred` hold frequently. -/
noncomputable def equiv (I : Interlace α)
    (freqP : ∀ n, ∃ m ≥ n, I.pred m) (freqnP : ∀ n, ∃ m ≥ n, ¬ I.pred m) :
    ℕ ≃ ℕ ⊕ ℕ :=
  .ofBijective I.e <| by
    refine ⟨fun m n h ↦ ?_, fun mn ↦ ?_⟩
    · simp only [e] at h
      have Hi := I.Hi -- for `grind`
      have Hj := I.Hj
      split_ifs at h with hm hn hn <;> refine le_antisymm ?_ ?_
      all_goals
        by_contra! H
        have H₁ := mono_i I H -- for `grind`
        have H₂ := mono_j I H
        grind
    · cases mn with
      | inl val =>
        obtain ⟨n, hn₁, hn₂⟩ := surjective_i' freqP val
        exact ⟨n, by grind⟩
      | inr val =>
        obtain ⟨n, hn₁, hn₂⟩ := surjective_j' freqnP val
        exact ⟨n, by grind⟩

end Interlace

/-!
### Basic definitions and properties

We state the "undergraduate" definitions of
* convergence of a (real) sequence to a limit (`ConditionalConvergence.SeqLim`)
* convergence of a series to a limit (`ConditionalConvergence.SeriesLim`)
* divergence of a series to +infinity (`ConditionalConvergence.SeriesDivToInfty`)

and prove the properties we need:
* any tail of a properly divergent series is also properly divergent;
* a series with nonnegative terms that does not diverge is bounded;
* if a series converges, then its terms tend to zero.

-/

open Finset

/-- The sequence `a` converges to `L`. -/
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/-- The series with terms `a n` converges to `L`. -/
def SeriesLim (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |∑ k ∈ range n, a k - L| < ε

/-- The series with terms `a n` diverges to `+∞`. -/
def SeriesDivToInfty (a : ℕ → ℝ) : Prop := ∀ K, ∃ N, ∀ n ≥ N, K < ∑ k ∈ range n, a k

lemma TailDivToInfty {a : ℕ → ℝ} (ha : SeriesDivToInfty a) (N₀ : ℕ) (K : ℝ) :
    ∃ N ≥ N₀, ∀ n ≥ N, K < ∑ k ∈ Ico N₀ n, a k := by
  obtain ⟨N, hN⟩ := ha (K + ∑ k ∈ range N₀, a k)
  refine ⟨max N₀ N, N₀.le_max_left N, fun n hn ↦ ?_⟩
  specialize hN n (le_of_max_le_right hn)
  rw [← sum_range_add_sum_Ico _ (le_of_max_le_left hn)] at hN
  linarith

lemma SeriesBounded_of_nonneg_and_not_divToInfty {a : ℕ → ℝ} (ha₀ : 0 ≤ a)
    (ha : ¬ SeriesDivToInfty a) :
    ∃ M, ∀ n, |∑ k ∈ range n, a k| ≤ M := by
  unfold SeriesDivToInfty at ha
  push_neg at ha
  obtain ⟨M, hM⟩ := ha
  refine ⟨M, fun n ↦ ?_⟩
  obtain ⟨m, hm₁, hm₂⟩ := hM n
  rw [abs_of_nonneg <| sum_nonneg fun i a ↦ ha₀ i]
  rw [← sum_range_add_sum_Ico _ hm₁] at hm₂
  have : 0 ≤ ∑ k ∈ Ico n m, a k := sum_nonneg fun i a ↦ ha₀ i
  grind

lemma SeqLim_zero_of_SeriesLim {a : ℕ → ℝ} {L : ℝ} (h : SeriesLim a L) : SeqLim a 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hN₁ := hN n (by grind)
  have hN₂ := hN (n + 1) (by grind)
  rw [sum_range_succ, add_sub_right_comm, add_comm] at hN₂
  set x := ∑ x ∈ range n, a x - L
  grw [← abs_sub_abs_le_abs_add] at hN₂
  rw [sub_zero]
  linarith

/-!
### Second half of the construction/proof

In this part, we show that, given two sequences `a b : ℕ → ℝ` with nonnegative terms
that both tend to zero and whose corresponding series both tend to infinity, and `L : ℝ`,
there is an equivalence `e : ℕ ≃ ℕ ⊕ ℕ` such that the series obtained by interleaving
`a` and `-b` according to `e` converges to `L`.
-/

/-- This structure captures the state of the recursive construction. -/
structure state (a b : ℕ → ℝ) where
  /-- next index in the first sequence -/
  i₁ : ℕ
  /-- next index in the second sequece -/
  i₂ : ℕ
  /-- total signed sum -/
  sum : ℝ

/-- Define a sequence of states according to the algorithm in the proof. -/
@[grind, simp]
noncomputable def seqState (a b : ℕ → ℝ) (L : ℝ) :
    ℕ → state a b
  | 0 => { i₁ := 0, i₂ := 0, sum := 0 }
  | n + 1 =>
      let st := seqState a b L n
      -- we take the next term from `a` if `s < L`, else from `-b`
      if st.sum < L then { i₁ := st.i₁ + 1, i₂ := st.i₂, sum := st.sum + a st.i₁ }
                    else { i₁ := st.i₁, i₂ := st.i₂ + 1, sum := st.sum - b st.i₂ }

namespace seqState

/-- The sequence of `state`s used below. -/
noncomputable abbrev ss (a b : ℕ → ℝ) (L : ℝ) : ℕ → state a b := seqState a b L

/-- Translate this into an `Interlace` structure. -/
@[grind]
noncomputable def interlace (a b : ℕ → ℝ) (L : ℝ) : Interlace (state a b) where
  s := ss a b L
  i n := (ss a b L n).i₁
  j n := (ss a b L n).i₂
  P n st := st.sum < L

open Interlace

@[grind =]
lemma interlace_pred (a b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    (interlace a b L).pred n ↔ (seqState a b L n).sum < L := by
  rfl

lemma aux_i₁ (a b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    letI st := seqState a b L
    ∀ m ≥ n, (∀ k ∈ Ico n m, (st k).sum < L) → (st m).i₁ = (st n).i₁ + (m - n) ∧
      (st m).sum = (st n).sum + ∑ x ∈ range (m - n), a ((st n).i₁ + x) := by
  set st := seqState a b L
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hmn ih =>
    intro h
    have h₁ := h m (by grind)
    obtain ⟨ih₁, ih₂⟩ := ih (by grind)
    have H : (st (m + 1)).i₁ = (st n).i₁ + (m + 1 - n) := by grind
    refine ⟨H, ?_⟩
    have : (st (m + 1)).sum = (st m).sum + a (st m).i₁ := by grind
    rw [this, ih₂, show m + 1 - n = m - n + 1 by grind, sum_range_succ, ih₁]
    ring

lemma aux_i₂ (a b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    letI st := seqState a b L
    ∀ m ≥ n, (∀ k ∈ Ico n m, L ≤ (st k).sum) → (st m).i₂ = (st n).i₂ + (m - n) ∧
      (st m).sum = (st n).sum - ∑ k ∈ range (m - n), b ((st n).i₂ + k) := by
  set st := seqState a b L
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hmn ih =>
    intro h
    have h₁ := h m (by grind)
    obtain ⟨ih₁, ih₂⟩ := ih (by grind)
    have H : (st (m + 1)).i₂ = (st n).i₂ + (m + 1 - n) := by grind
    refine ⟨H, ?_⟩
    have : (st (m + 1)).sum = (st m).sum - b (st m).i₂ := by grind
    rw [this, ih₂, show m + 1 - n = m - n + 1 by grind, sum_range_succ, ih₁]
    ring

lemma frequently_lt (a : ℕ → ℝ) {b : ℕ → ℝ} (hb : SeriesDivToInfty b) (L : ℝ) (n : ℕ) :
    ∃ m ≥ n, (seqState a b L m).sum < L := by
  set st := seqState a b L
  by_contra! H
  have h : ∀ m ≥ n, (st m).sum = (st n).sum - ∑ k ∈ range (m - n), b ((st n).i₂ + k) :=
    fun m hm ↦ (aux_i₂ a b L n m hm (by grind)).2
  obtain ⟨N, hN₁, hN⟩ := TailDivToInfty hb (st n).i₂ ((st n).sum - L)
  specialize H (N + n) (by grind)
  specialize hN ((st n).i₂ + N) (by grind)
  rw [sum_Ico_eq_sum_range] at hN
  grind

lemma frequently_le {a : ℕ → ℝ} (ha : SeriesDivToInfty a) (b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    ∃ m ≥ n, L ≤ (seqState a b L m).sum := by
  set st := seqState a b L
  by_contra! H
  have h : ∀ m ≥ n, (st m).sum = (st n).sum + ∑ k ∈ range (m - n), a ((st n).i₁ + k) :=
    fun m hm ↦ (aux_i₁ a b L n m hm (by grind)).2
  obtain ⟨N, hN₁, hN⟩ := TailDivToInfty ha (st n).i₁ (L - (st n).sum)
  specialize H (N + n) (by grind)
  specialize hN ((st n).i₁ + N) (by grind)
  rw [sum_Ico_eq_sum_range] at hN
  grind

lemma frequently_le' {a : ℕ → ℝ} (ha : SeriesDivToInfty a) (b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    ∃ m ≥ n, ¬ (seqState a b L m).sum < L := by
  convert frequently_le ha b L n
  simp

lemma frequently_lt_then_le {a b : ℕ → ℝ} (ha : SeriesDivToInfty a) (hb : SeriesDivToInfty b)
    (L : ℝ) (n : ℕ) :
    ∃ m ≥ n, (seqState a b L m).sum < L ∧ L ≤ (seqState a b L (m + 1)).sum := by
  by_contra! H
  obtain ⟨m, hm₁, hm₂⟩ := frequently_lt a hb L n
  have H : ∀ k ≥ m, (seqState a b L k).sum < L := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hm₂
    | succ k hk ih => grind
  obtain ⟨k, hk₁, hk₂⟩ := frequently_le ha b L m
  grind

lemma seqLim_aux {a b : ℕ → ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (L : ℝ) (n : ℕ) :
    |(seqState a b L (n + 1)).sum - L| ≤
    max |(seqState a b L n).sum - L| (max (a (seqState a b L n).i₁) (b (seqState a b L n).i₂)) := by
  have abs_aux {x y : ℝ} (hx : x ≤ 0) (hy : 0 ≤ y) : |x + y| ≤ max |x| y := by grind
  simp only [seqState]
  split_ifs with h <;> simp only
  · rw [add_sub_right_comm]
    grw [abs_aux (by grind) (ha₀ _)]
    gcongr
    exact le_max_left ..
  · rw [← neg_add_eq_sub (b _), ← add_sub]
    grw [abs_aux (neg_nonpos.mpr <| (hb₀ _)) (by grind)]
    rw [max_comm, abs_neg, abs_of_nonneg (hb₀ _)]
    gcongr
    exacts [le_abs_self _, le_max_right ..]

lemma seqLim {a b : ℕ → ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha₁ : SeqLim a 0)
    (hb₁ : SeqLim b 0) (ha₂ : SeriesDivToInfty a) (hb₂ : SeriesDivToInfty b) (L : ℝ) :
    SeqLim (fun n ↦ (seqState a b L n).sum) L := by
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha₁ ε hε
  obtain ⟨Nb, hNb⟩ := hb₁ ε hε
  simp only [sub_zero, abs_of_nonneg (ha₀ _), abs_of_nonneg (hb₀ _)] at hNa hNb
  obtain ⟨Na', hNa'⟩ := (interlace a b L).surjective_i (frequently_lt a hb₂ L) Na
  obtain ⟨Nb', hNb'⟩ := (interlace a b L).surjective_j (frequently_le' ha₂ b L) Nb
  simp only [interlace] at hNa' hNb'
  obtain ⟨N, hN₁, hN₂⟩ := frequently_lt_then_le ha₂ hb₂ L (max Na' Nb')
  refine ⟨N, fun n hn ↦ ?_⟩
  dsimp only at *
  induction n, hn using Nat.le_induction with
  | base =>
    have : a (seqState a b L N).i₁ < ε := hNa _ <| hNa' ▸ (mono_i (interlace a b L) <| by grind)
    grind
  | succ n hn ih =>
    have H := seqLim_aux ha₀ hb₀ L n
    have Ha : a (seqState a b L n).i₁ < ε := hNa _ <| hNa' ▸ (mono_i (interlace a b L) <| by grind)
    have Hb : b (seqState a b L n).i₂ < ε := hNb _ <| hNb' ▸ (mono_j (interlace a b L) <| by grind)
    grind

lemma sum_eq_seqState_sum (a b : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    ∑ k ∈ range n, Sum.elim a (-b) ((interlace a b L).e k) = (seqState a b L n).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases! H : (seqState a b L n).sum < L
    · suffices a ((interlace a b L).i n) = a (seqState a b L n).i₁ by
        simp [e, interlace_pred, H, this]
      rfl
    · rw [← not_lt] at H
      suffices b ((interlace a b L).j n) = b (seqState a b L n).i₂ by
        simp [e, interlace_pred, H, sub_eq_add_neg, this]
      rfl

noncomputable
abbrev equiv {a b : ℕ → ℝ} (ha : SeriesDivToInfty a) (hb : SeriesDivToInfty b) (L : ℝ) :
    ℕ ≃ ℕ ⊕ ℕ :=
  (interlace a b L).equiv (frequently_lt a hb L) (frequently_le' ha b L)

end seqState

open seqState in
/--
The main result for the second part:

if we have two nonnegative sequences `a b : ℕ → ℝ` such that `a → 0` and `b → 0`
and `∑ a = +∞`, `∑ b = +∞`, and `L : ℝ`, we can interlace `a` and `-b` to obtain
a series converging to `L`.
-/
theorem exists_equiv_to_sum_seriesLim {a b : ℕ → ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha₁ : SeqLim a 0) (hb₁ : SeqLim b 0) (ha₂ : SeriesDivToInfty a) (hb₂ : SeriesDivToInfty b)
    (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ ⊕ ℕ, SeriesLim ((Sum.elim a (-b)) ∘ σ) L := by
  use equiv ha₂ hb₂ L
  intro ε hε
  simp only [Function.comp_apply, seqState.equiv, Interlace.equiv, Equiv.ofBijective_apply]
  obtain ⟨N, hN⟩ := seqLim ha₀ hb₀ ha₁ hb₁ ha₂ hb₂ L ε hε
  exact ⟨N, fun n hn ↦ by simpa only [sum_eq_seqState_sum] using hN _ hn⟩

/-!
### The first part of the construction/proof

In this part, we show that if we split a given sequence `c : ℕ → ℝ` with the property
that its corresponding series converges, but does not converge absolutely, into the subsequences
consisting of the nonnegative and the (positively taken) negative terms, respectively,
then this pair of sequences satisfies the conditions for the second part.
-/

/-- This structure captures the state of the recursive construction. -/
structure state' (c : ℕ → ℝ) where
  /-- next index for nonnegative terms -/
  ige : ℕ
  /-- next index for negative terms -/
  ilt : ℕ

/-- Define a sequence of `state'`s splitting the given sequence into its `≥ 0` and `< 0` terms. -/
@[grind, simp]
noncomputable def splitSeq (c : ℕ → ℝ) : ℕ → state' c
  | 0 => { ige := 0, ilt := 0 }
  | n + 1 =>
    let st := splitSeq c n
    if 0 ≤ c n then { ige := st.ige + 1, ilt := st.ilt }
               else { ige := st.ige, ilt := st.ilt + 1}

namespace splitSeq

/-- The sequence of `state'`s used below. -/
noncomputable abbrev ss (c : ℕ → ℝ) : ℕ → state' c := splitSeq c

/-- Translate this into an `Interlace` structure. -/
@[grind]
noncomputable def interlace (c : ℕ → ℝ) : Interlace (state' c) where
  s := ss c
  i n := (ss c n).ige
  j n := (ss c n).ilt
  P n st := 0 ≤ c n

variable {c : ℕ → ℝ} (hc₁ : ∃ L, SeriesLim c L) (hc₂ : SeriesDivToInfty (|c ·|))

include hc₁ hc₂

lemma frequently_ge (n : ℕ) : ∃ m ≥ n, 0 ≤ c m := by
  by_contra! H
  obtain ⟨L, hL⟩ := hc₁
  obtain ⟨N, hN⟩ := hc₂ (∑ k ∈ range n, c k + ∑ k ∈ range n, |c k| - L + 1)
  obtain ⟨N', hN'⟩ := hL 1 zero_lt_one
  specialize hN (max n (max N N')) (by grind)
  specialize hN' (max n (max N N')) (by grind)
  dsimp only at *
  have H₁ : ∑ k ∈ Ico n (max n (max N N')), |c k| = -∑ k ∈ Ico n (max n (max N N')), c k := by
    simpa only [← sum_neg_distrib] using sum_congr rfl (by grind)
  rw [← sum_range_add_sum_Ico _ (m := n) (by grind)] at hN'
  conv_rhs at hN => rw [← sum_range_add_sum_Ico _ (m := n) (by grind)]
  grind

lemma frequently_lt (n : ℕ) : ∃ m ≥ n, c m < 0 := by
  by_contra! H
  obtain ⟨L, hL⟩ := hc₁
  obtain ⟨N, hN⟩ := hc₂ (-∑ k ∈ range n, c k + ∑ k ∈ range n, |c k| + L + 1)
  obtain ⟨N', hN'⟩ := hL 1 zero_lt_one
  specialize hN (max n (max N N')) (by grind)
  specialize hN' (max n (max N N')) (by grind)
  dsimp only at *
  have H₁ : ∑ k ∈ Ico n (max n (max N N')), |c k| = ∑ k ∈ Ico n (max n (max N N')), c k :=
    sum_congr rfl (by grind)
  rw [← sum_range_add_sum_Ico _ (m := n) (by grind)] at hN'
  conv_rhs at hN => rw [← sum_range_add_sum_Ico _ (m := n) (by grind)]
  grind

lemma frequently_lt' (n : ℕ) : ∃ m ≥ n, ¬ 0 ≤ c m := by
  convert frequently_lt hc₁ hc₂ n
  simp

/-- The bijection extracted from the seuqence of `state'`s -/
noncomputable abbrev equiv : ℕ ≃ ℕ ⊕ ℕ :=
  (interlace c).equiv (frequently_ge hc₁ hc₂) <| frequently_lt' hc₁ hc₂

/-- The subsequence of `c` consisting of its nonnegative terms. -/
noncomputable def seq_ge : ℕ → ℝ :=
  c ∘ (equiv hc₁ hc₂).symm ∘ .inl

/-- The subsequence of `c` consisting of its negative terms. -/
noncomputable def seq_lt : ℕ → ℝ :=
  (- ·) ∘ c ∘ (equiv hc₁ hc₂).symm ∘ .inr

section

omit hc₁ hc₂

@[grind =]
lemma interlace_pred (c : ℕ → ℝ) (n : ℕ) : (interlace c).pred n ↔ 0 ≤ c n := by
  rfl

end

open Interlace

lemma seq_ge_spec {n : ℕ} (hc : 0 ≤ c n) : seq_ge hc₁ hc₂ (splitSeq c n).ige = c n := by
  have : (equiv hc₁ hc₂).symm (.inl (splitSeq c n).ige) = n := by
    rw [← interlace_pred] at hc
    suffices (splitSeq c n).ige = (interlace c).i n by
      simp [Equiv.symm_apply_eq, equiv, Interlace.equiv, e, hc, this]
    rfl
  simp [seq_ge, this]

lemma seq_lt_spec {n : ℕ} (hc : c n < 0) : seq_lt hc₁ hc₂ (splitSeq c n).ilt = -(c n) := by
  have : (equiv hc₁ hc₂).symm (.inr (splitSeq c n).ilt) = n := by
    rw [← not_le, ← interlace_pred] at hc
    suffices (splitSeq c n).ilt = (interlace c).j n by
      simp [Equiv.symm_apply_eq, equiv, Interlace.equiv, e, hc, this]
    rfl
  simp [seq_lt, this]

lemma nonneg_ge : 0 ≤ seq_ge hc₁ hc₂ := by
  refine Pi.le_def.mpr fun n ↦ ?_
  have H₁ := Equiv.apply_symm_apply (equiv hc₁ hc₂) <| .inl n
  simp only [equiv, Interlace.equiv, Equiv.ofBijective_apply] at H₁
  have {n i : ℕ} (h : (interlace c).e n = .inl i) : 0 ≤ c n := by grind
  simpa [seq_ge] using this H₁

lemma nonneg_lt : 0 ≤ seq_lt hc₁ hc₂ := by
  refine Pi.le_def.mpr fun n ↦ ?_
  have H₁ := Equiv.apply_symm_apply (equiv hc₁ hc₂) <| .inr n
  simp only [equiv, Interlace.equiv, Equiv.ofBijective_apply] at H₁
  have {n i : ℕ} (h : (interlace c).e n = .inr i) : c n ≤ 0 := by grind
  simpa [seq_lt] using this H₁

lemma seqLim_zero : SeqLim (seq_ge hc₁ hc₂) 0 ∧ SeqLim (seq_lt hc₁ hc₂) 0 := by
  have H := eventually_le (equiv hc₁ hc₂).symm
  obtain ⟨L, hL⟩ := hc₁
  refine ⟨fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  all_goals
    obtain ⟨N, hN⟩ := SeqLim_zero_of_SeriesLim hL ε hε
    obtain ⟨n, hn⟩ := H N
    refine ⟨n, fun m hm ↦ ?_⟩
    simp [seq_ge, seq_lt]
    grind

lemma sum_range_abs_eq_sum_add_sum (n : ℕ) :
    ∑ k ∈ range n, |c k| =
      ∑ i ∈ range (splitSeq c n).ige, seq_ge hc₁ hc₂ i +
      ∑ j ∈ range (splitSeq c n).ilt, seq_lt hc₁ hc₂ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]; clear ih
    by_cases h : 0 ≤ c n
    · simp only [abs_of_nonneg, splitSeq, h, ↓reduceIte, sum_range_succ, seq_ge_spec hc₁ hc₂ h]
      abel
    · simp only [splitSeq, h, ↓reduceIte, sum_range_succ, abs_of_neg <| not_le.mp h,
        seq_lt_spec hc₁ hc₂ <| not_le.mp h]
      abel

lemma sum_range_eq_sum_sub_sum (n : ℕ) :
    ∑ k ∈ range n, c k =
      ∑ i ∈ range (splitSeq c n).ige, seq_ge hc₁ hc₂ i -
      ∑ j ∈ range (splitSeq c n).ilt, seq_lt hc₁ hc₂ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]; clear ih
    by_cases h : 0 ≤ c n
    · simp only [splitSeq, h, ↓reduceIte, sum_range_succ, seq_ge_spec hc₁ hc₂ h]
      abel
    · simp only [splitSeq, h, ↓reduceIte, sum_range_succ, seq_lt_spec hc₁ hc₂ <| not_le.mp h]
      abel

lemma seriesDivToInfty : SeriesDivToInfty (seq_ge hc₁ hc₂) ∧ SeriesDivToInfty (seq_lt hc₁ hc₂) := by
  obtain ⟨L, hL⟩ := id hc₁ -- don't clear `hc₁`
  obtain ⟨N₁, hN₁⟩ := hL 1 zero_lt_one
  simp only [sum_range_eq_sum_sub_sum hc₁ hc₂] at hN₁
  constructor
  on_goal 1 =>
    by_contra! H
    obtain ⟨M, hM⟩ := SeriesBounded_of_nonneg_and_not_divToInfty (nonneg_ge hc₁ hc₂) H
    obtain ⟨N₂, hN₂⟩ := hc₂ (2 * M - L + 1)
  on_goal 2 =>
    by_contra! H
    obtain ⟨M, hM⟩ := SeriesBounded_of_nonneg_and_not_divToInfty (nonneg_lt hc₁ hc₂) H
    obtain ⟨N₂, hN₂⟩ := hc₂ (2 * M + L + 1)
  all_goals
    simp only [sum_range_abs_eq_sum_add_sum hc₁ hc₂] at hN₂
    specialize hN₁ (max N₁ N₂) (by grind)
    specialize hN₂ (max N₁ N₂) (by grind)
    grind

end splitSeq

open splitSeq in
/--
The **Conditional Convergence Theorem**:

If a series converges, but does not converge absolutely, then it can be rearranged to converge
to any desired limit `L : ℝ`.
-/
theorem exists_equiv_seriesLim {c : ℕ → ℝ} (hc₁ : ∃ L, SeriesLim c L)
    (hc₂ : SeriesDivToInfty (|c ·|)) (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ, SeriesLim (c ∘ σ) L := by
  obtain ⟨ha₁, hb₁⟩ := seqLim_zero hc₁ hc₂
  obtain ⟨ha₂, hb₂⟩ := seriesDivToInfty hc₁ hc₂
  obtain ⟨σ₁, hσ₁⟩ :=
    exists_equiv_to_sum_seriesLim (nonneg_ge hc₁ hc₂) (nonneg_lt  hc₁ hc₂) ha₁ hb₁ ha₂ hb₂ L
  use σ₁.trans (equiv hc₁ hc₂).symm
  convert hσ₁
  ext n
  simp only [Equiv.coe_trans, Function.comp_apply]
  cases σ₁ n with
  | inl val => simp [seq_ge]
  | inr val => simp [seq_lt]

end ConditionalConvergence
