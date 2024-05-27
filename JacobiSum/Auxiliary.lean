import Mathlib

section Auxiliary

/-!
### Auxiliary results
-/

lemma MulEquiv.orderOf_eq {M M' : Type*} [Monoid M] [Monoid M'] (e : M ≃* M') (m : M) :
    orderOf (e m) = orderOf m := by
  rcases (orderOf m).eq_zero_or_pos with h | h
  · rw [h]
    rw [orderOf_eq_zero_iff'] at h ⊢
    peel h with n h₀ hn
    contrapose! hn
    rwa [← map_pow, e.map_eq_one_iff] at hn
  · simp_rw [orderOf_eq_iff h, ← map_pow, ne_eq, e.map_eq_one_iff]
    exact (orderOf_eq_iff h).mp rfl

lemma Complex.norm_rootOfUnity_eq_one {ζ : ℂˣ} {n : ℕ+} (hζ : ζ ∈ rootsOfUnity n ℂ) :
    ‖(ζ : ℂ)‖ = 1 := by
  refine norm_eq_one_of_pow_eq_one ?_ <| n.ne_zero
  norm_cast
  rw [show ζ ^ (n : ℕ) = 1 from hζ]
  rfl

lemma GaussianInt.toComplex_injective : Function.Injective GaussianInt.toComplex :=
  (injective_iff_map_eq_zero _).mpr fun _ ↦ GaussianInt.toComplex_eq_zero.mp

/-- A version of `IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity` that takes a natural number `k`
as argument instead of a `PNat` -/
lemma IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity' {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (hk : 0 < k) {ζ : R} (hζ : IsPrimitiveRoot ζ k) {ξ : Rˣ}
    (hξ : ξ ∈ rootsOfUnity (⟨k, hk⟩ : ℕ+) R) :
    ∃ i < k, ζ ^ i = ξ := by
  have hζ' : IsUnit ζ := hζ.isUnit hk
  have hζ'' : IsPrimitiveRoot hζ'.unit (⟨k, hk⟩ : ℕ+) := isUnit_unit hk hζ
  obtain ⟨i, hi₁, hi₂⟩ := hζ''.eq_pow_of_mem_rootsOfUnity hξ
  refine ⟨i, hi₁, ?_⟩
  apply_fun ((↑) : Rˣ → R) at hi₂
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hi₂
--#check IsPrimitiveRoot.eq_pow_of_pow_eq_one

lemma Finset.sum_eq_sum_one_sub {R M : Type*} [Ring R] [Fintype R] [DecidableEq R]
    [AddCommMonoid M] (f : R → M) :
    Finset.sum univ f = Finset.sum univ fun x ↦ f (1 - x) := by
  refine Fintype.sum_bijective (fun x : R ↦ 1 - x) ?_ _ _ fun x ↦ ?_
  · refine Function.Involutive.bijective ?_
    simp only [Function.Involutive, sub_sub_cancel, implies_true]
  · simp only [sub_sub_cancel, mul_comm]

lemma Algebra.adjoin.sub_one_dvd_pow_sub_one (R : Type*) {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (μ : A) (k : ℕ) :
    ∃ z ∈ adjoin R {μ}, μ ^ k - 1 = z * (μ - 1) := by
  refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

variable {R : Type*} [CommRing R] [IsDomain R]

open BigOperators Polynomial in
/-- A version of `X_pow_sub_C_eq_prod` for integral domains instead of fields. -/
lemma X_pow_sub_C_eq_prod'
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i ∈ Finset.range n, (X - C (ζ ^ i * α)) := by
  let K := FractionRing R
  have := X_pow_sub_C_eq_prod (hζ.map_of_injective <| NoZeroSMulDivisors.algebraMap_injective R K)
    hn <| map_pow (algebraMap R K) α n ▸ congrArg (algebraMap R K) e
  apply_fun Polynomial.map <| algebraMap R K using
    map_injective (algebraMap R K) <| NoZeroSMulDivisors.algebraMap_injective R K
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul] using this

open Finset Polynomial in
lemma IsPrimitiveRoot.prod_eq_order {n : ℕ} (hn : n ≠ 0) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    (-1) ^ (n - 1) * (range (n - 1)).prod (fun k ↦ μ ^ (k + 1) - 1) = n := by
  suffices H : (range (n - 1)).prod (fun k ↦ 1 - μ ^ (k + 1)) = n by
    rw [← H]
    have : (-1 : R) ^ (n - 1) = (range (n - 1)).prod (fun k ↦ -1) := by
      rw [prod_const, card_range]
    rw [this, ← prod_mul_distrib]
    simp only [neg_one_mul, neg_sub]
  have := X_pow_sub_C_eq_prod' hμ (Nat.pos_of_ne_zero hn) (one_pow n)
  have HH : (X ^ n - C 1 : R[X]) = (X - C 1) * (range n).sum (fun k ↦ X ^ k) :=
    (mul_geom_sum X n).symm
  rw [HH] at this; clear HH
  let m + 1 := n
  rw [prod_range_succ', pow_zero, mul_one, mul_comm, eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this
  simpa only [Nat.cast_add, Nat.cast_one, mul_one, map_pow, eval_prod, eval_sub, eval_X, eval_pow,
    eval_C, eval_geom_sum, one_pow, sum_const, card_range, nsmul_eq_mul] using this

lemma IsPrimitiveRoot.order_eq_mul {n : ℕ} (hn : 2 < n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, n = z * (μ - 1) ^ 2 := by
  have := hμ.prod_eq_order (by omega : n ≠ 0)
  let m + 3 := n
  simp only [Nat.add_succ_sub_one, Nat.cast_add, Nat.cast_ofNat] at this
  rw [Finset.prod_range_succ', Finset.prod_range_succ'] at this
  refine ⟨(-1) ^ (m + 2) * ((Finset.range m).prod fun k ↦ μ ^ (k + 1 + 1 + 1) - 1) * (μ + 1),
    ?_, ?_⟩
  · refine Subalgebra.mul_mem _ ?_ <|
      Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) <| Subalgebra.one_mem _
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_
    · exact Subalgebra.neg_mem _ <| Subalgebra.one_mem _
    · refine Subalgebra.prod_mem _ fun k _ ↦ Subalgebra.sub_mem _ ?_ <| Subalgebra.one_mem _
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) _
  · push_cast
    rw [← this]
    ring

end Auxiliary


section Generator

/-!
### Generators of groups and homomorphisms

A few helpful statements about group generators and monoid homomorphisms.
-/

/-- A *generator* of a group `G` is an element of `G` such that the subgroup
generated by it is the full group. -/
structure Group.Generator (G : Type*) [Group G] where
  val : G
  generates : ∀ x, x ∈ Subgroup.zpowers val

attribute [coe] Group.Generator.val

instance {G : Type u} [Group G] : Coe (Group.Generator G) G where
  coe := Group.Generator.val

variable {G G' : Type*} [Group G] [Group G'] (g : Group.Generator G)

/-- Two group homomorphisms `G → G'` are equal if and only if they agree on a generator of `G`. -/
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g.val, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp <| g.generates x
  rw [← hn, map_zpow, map_zpow, H]

/-- A generator of a cyclic group. -/
noncomputable def IsCyclic.generator (h : IsCyclic G) : Group.Generator G :=
  ⟨Classical.choose h.exists_generator, Classical.choose_spec h.exists_generator⟩

namespace Group.Generator

lemma isCyclic : IsCyclic G where
  exists_generator := ⟨g.val, g.generates⟩

lemma orderOf_eq_natCard : orderOf (g : G) = Nat.card G := by
  rcases eq_or_ne (Nat.card G) 0 with h | h
  · rw [h]
    have : Infinite G := (Nat.card_eq_zero.mp h ).resolve_left <| not_isEmpty_of_nonempty G
    exact Infinite.orderOf_eq_zero_of_forall_mem_zpowers g.generates
  · have : Fintype G := @Fintype.ofFinite G <| Nat.finite_of_card_ne_zero h
    rw [Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers g.generates

variable {g} {g' : G'} (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a unique homomorphism `G → G'` mapping `g` to `g'`. -/
noncomputable
def monoidHom : G →* G' where
  toFun x := g' ^ (Classical.choose <| Subgroup.mem_zpowers_iff.mp <| g.generates x)
  map_one' := orderOf_dvd_iff_zpow_eq_one.mp <|
    (Int.natCast_dvd_natCast.mpr hg').trans <| orderOf_dvd_iff_zpow_eq_one.mpr <|
    Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| g.generates 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
    rw [← zpow_eq_zpow_iff_modEq, zpow_add]
    simp only [fun x ↦ Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| g.generates x]

lemma monoidHom_apply_gen : monoidHom hg' g = g' := by
  simp only [monoidHom, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq, zpow_one]
  exact Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| g.generates g.val

lemma monoidHom_ex_unique : ∃! f : G →* G', f g = g' := by
  refine ⟨monoidHom hg', monoidHom_apply_gen hg', fun f h ↦ ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator g, h, monoidHom_apply_gen hg']

/-- If two groups are cyclic of the same order, they are isomorphic. -/
noncomputable
def mulEquiv_of_orderOf_eq {g' : Generator G'} (h : orderOf (g : G) = orderOf (g' : G')) :
    G ≃* G' :=
  @mulEquivOfCyclicCardEq _ _ _ _ g.isCyclic g'.isCyclic <|
    orderOf_eq_natCard g ▸ orderOf_eq_natCard g' ▸ h

end Group.Generator

end Generator

/- /-!
### Auxiliary results on self-maps of finsets
-/

namespace Finset

/-- If a function `f` maps a `Finset` into itself, all its iterates do so as well. -/
lemma iterate_mem {α} {s : Finset α} {f : α → α}
    (hf : ∀ a ∈ s, f a ∈ s) (n : ℕ) {a : α} (ha : a ∈ s) : f^[n] a ∈ s := by
  induction' n with n ih
  · simp [ha]
  · simp only [Function.iterate_succ', Function.comp_apply, ih, hf]

open Function Equiv in
/-- We can turn a function `f` that maps a `Finset` `s` into itself and has order dividing `n`
when restricted to `s` into an equivalence of `s` considered as a type. -/
def equivOfFiniteOrderOn {α} {s : Finset α} {f : α → α} (hf : ∀ a ∈ s, f a ∈ s) {n : ℕ}
    (hn : 1 ≤ n) (h : ∀ a ∈ s, f^[n] a = a) : Equiv s s := by
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨f a, hf a ha⟩, fun ⟨a, ha⟩ ↦ ⟨f^[n - 1] a, iterate_mem hf _ ha⟩,
     leftInverse_iff_comp.mpr ?_, leftInverse_iff_comp.mpr ?_⟩ <;>
  { ext a
    simpa only [comp_apply, id_eq, ← iterate_succ_apply, ← iterate_succ_apply' (f := f),
      ← Nat.succ_sub hn, Nat.succ_sub_one] using h a.val a.prop }

@[simp]
lemma equivOf_apply {α} {s : Finset α} {f : α → α} (hf : ∀ a ∈ s, f a ∈ s) {n : ℕ}
    (hn : 1 ≤ n) (h : ∀ a ∈ s, f^[n] a = a) (a : {x // x ∈ s}) :
    equivOfFiniteOrderOn hf hn h a = ⟨f a.val, hf a.val a.prop⟩ := rfl

open Function Equiv in
/-- The `m`th power of an equivalence on `s` obtained by restricting a function `f`
can be obtained by restricting the `m`th iterate of `f`. -/
lemma equivOf_pow_eq_iterate {α} {s : Finset α} {f : α → α} (hf : ∀ a ∈ s, f a ∈ s) {n : ℕ}
    (hn : 1 ≤ n) (h : ∀ a ∈ s, f^[n] a = a) (m : ℕ) (a : {x // x ∈ s}) :
    ((equivOfFiniteOrderOn hf hn h) ^ m) a = ⟨f^[m] a, iterate_mem hf m a.prop⟩ := by
  induction' m with m ih
  · simp only [Nat.zero_eq, pow_zero, Perm.coe_one, id_eq, iterate_zero, Subtype.coe_eta]
  · rw [pow_succ', Perm.coe_mul, comp_apply, equivOf_apply, Subtype.mk.injEq, ih, iterate_succ_apply']

open Function Equiv in
/-- If `f` has order dividing `n` and maps a `Finset` `s` into itself, then the equivalence
on `s` obtained by restricting `f` also has order dividing `n`. -/
lemma equivOf_order {α} {s : Finset α} {f : α → α} (hf : ∀ a ∈ s, f a ∈ s) {n : ℕ}
    (hn : 1 ≤ n) (h : ∀ a ∈ s, f^[n] a = a) :
    (equivOfFiniteOrderOn hf hn h) ^ n = 1 := by
  ext a
  simpa only [equivOf_pow_eq_iterate, coe_one, id_eq] using h a.val a.prop

open Function Equiv Perm in
/-- If `f : α → α` maps a `Finset` `s` to itself and its `p^n`th iterate is the identity on `s`,
where `p` is a prime number, then the cardinality of `s` is congruent mod `p` to the number of
fixed points of `f` on `s` . -/
lemma card_fixedPoints_modEq {α} [Fintype α] [DecidableEq α] {s : Finset α} {f : α → α}
    (hf : ∀ a ∈ s, f a ∈ s) {p n : ℕ} [hp : Fact p.Prime] (h : ∀ a ∈ s, f^[p ^ n] a = a) :
    s.card ≡ (s.filter fun a ↦ f a = a).card [MOD p] := by
  have hpn : 1 ≤ p ^ n := n.one_le_pow p hp.out.one_lt.le
  suffices : (s.filter fun a ↦ f a = a).card = (support <| equivOfFiniteOrderOn hf hpn h)ᶜ.card
  · convert Fintype.card_coe s ▸ (card_compl_support_modEq <| equivOf_order hf hpn h).symm
  refine (card_congr (fun (x : { x // x ∈ s }) _ ↦ x.val) (fun a ha ↦ ?_)
    (fun _ _ _ _ ↦ SetCoe.ext) (fun _ hb ↦ ?_)).symm
  · simp only [mem_compl, Perm.mem_support, coe_fn_mk, ne_eq, not_not, mem_filter, coe_mem,
      true_and] at ha ⊢
    exact congr_arg Subtype.val ha
  · simpa only [mem_filter, mem_compl, Perm.mem_support, equivOf_apply, ne_eq, not_not,
      exists_prop, Subtype.exists, Subtype.mk.injEq, exists_and_left, exists_eq_right_right]
      using hb

/-- If `f : α → α` maps a `Finset` `s` to itself and its `p`th iterate is the identity on `s`,
where `p` is a prime number, then the cardinality of `s` is congruent mod `p` to the number of
fixed points of `f` on `s` . -/
lemma card_fixedPoints_modEq_prime {α} [Fintype α] [DecidableEq α] {s : Finset α} {f : α → α}
    (hf : ∀ a ∈ s, f a ∈ s) {p : ℕ} [Fact p.Prime] (h : ∀ a ∈ s, f^[p] a = a) :
    s.card ≡ (s.filter fun a ↦ f a = a).card [MOD p] :=
  card_fixedPoints_modEq hf <| (pow_one p).symm ▸ h

/-- Write the sum of `f` over a finset `s` as an `ℕ`-linear combination of its values. -/
lemma sum_eq_sum_card_nsmul {α β} [DecidableEq α] [AddCommMonoid β] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.sum f = (s.image f).sum fun x ↦ (s.filter (f · = x)).card • x := by
  convert (sum_image' f fun x _ ↦ ?_).symm
  have H : ∀ y ∈ s.filter (f · = f x), f y = f x := fun _ hy ↦ (mem_filter.mp hy).2
  rw [sum_congr rfl H, sum_const]

/-- Write the sum of `f` over a finset `s` as an `ℕ`-linear combination of its values. -/
lemma sum_eq_sum_card_nsmul' {α β} [DecidableEq α] [AddCommMonoid β] [DecidableEq β]
    {s : Finset α} {t : Finset β} (f : α → β) (hst : ∀ a ∈ s, f a ∈ t) :
    s.sum f = t.sum fun x ↦ (s.filter (f · = x)).card • x := by
  rw [sum_eq_sum_card_nsmul]
  refine sum_subset (image_subset_iff.mpr hst) fun x _ hxs ↦ ?_
  have : s.filter (f · = x) = ∅ := by
    simp only [mem_image, not_exists, not_and] at hxs
    exact filter_eq_empty_iff.mpr hxs
  simp only [this, card_empty, zero_smul]

end Finset -/
