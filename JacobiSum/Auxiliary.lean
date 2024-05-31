import Mathlib


variable {G G' : Type*} [Group G] [Group G'] {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) {g' : G'}

lemma orderOf_generator_eq_natCard :
    orderOf g = Nat.card G := by
  rcases eq_or_ne (Nat.card G) 0 with h | h
  · rw [h]
    have : Infinite G := (Nat.card_eq_zero.mp h).resolve_left <| not_isEmpty_of_nonempty G
    exact Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg
  · have : Fintype G := @Fintype.ofFinite G <| Nat.finite_of_card_ne_zero h
    rw [Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
-- #find_home orderOf_generator_eq_natCard -- Mathlib.GroupTheory.SpecificGroups.Cyclic

/-- Two group homomorphisms `G → G'` are equal if and only if they agree on a generator of `G`. -/
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp <| hg x
  rw [← hn, map_zpow, map_zpow, H]
-- #find_home MonoidHom.eq_iff_eq_on_generator -- Mathlib.Algebra.Group.Subgroup.ZPowers

/-- If two groups are cyclic of the same order, they are isomorphic. -/
noncomputable
def mulEquiv_of_orderOf_eq (hg' : ∀ x, x ∈ Subgroup.zpowers g') (h : orderOf g = orderOf g') :
    G ≃* G' :=
  @mulEquivOfCyclicCardEq _ _ _ _ ⟨g, hg⟩ ⟨g', hg'⟩ <|
    orderOf_generator_eq_natCard hg ▸ orderOf_generator_eq_natCard hg' ▸ h

variable (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a homomorphism `G → G'` mapping `g` to `g'`. -/
noncomputable
def monoidHom_of_generates : G →* G' where
  toFun x := g' ^ (Classical.choose <| Subgroup.mem_zpowers_iff.mp <| hg x)
  map_one' := orderOf_dvd_iff_zpow_eq_one.mp <|
                (Int.natCast_dvd_natCast.mpr hg').trans <| orderOf_dvd_iff_zpow_eq_one.mpr <|
                Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
    rw [← zpow_eq_zpow_iff_modEq, zpow_add]
    simp only [fun x ↦ Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| hg x]

lemma monoidHom_of_generates_apply_gen : monoidHom_of_generates hg hg' g = g' := by
  simp only [monoidHom_of_generates, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq, zpow_one]
  exact Classical.choose_spec <| Subgroup.mem_zpowers_iff.mp <| hg g
