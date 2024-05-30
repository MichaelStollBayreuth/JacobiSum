import JacobiSum.Auxiliary

/-!
### Auxiliary results on multiplicative characters
-/

namespace MulChar

section General

variable {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']

lemma map_unit (χ : MulChar R R') (a : Rˣ) : IsUnit (χ a) :=
  IsUnit.map χ <| a.isUnit

lemma equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) :
    equivToUnitHom (χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a := by
  apply_fun ((↑) : R'ˣ → R') using Units.ext
  push_cast
  simp_rw [coe_equivToUnitHom]
  rfl

/-- The equivalence between multiplicative characters and homomorphisms of unit groups
as a multiplicative equivalence. -/
noncomputable
def mulEquivToUnitHom : MulChar R R' ≃* (Rˣ →* R'ˣ) :=
  { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }

/-- Two multiplicative characters on a monoid whose unit group is generated by `g`
are equal if and only if they agree on `g`. -/
lemma eq_iff (g : Group.Generator Rˣ) (χ₁ χ₂ : MulChar R R') :
    χ₁ = χ₂ ↔ χ₁ g.val = χ₂ g.val := by
  refine (Equiv.apply_eq_iff_eq equivToUnitHom).symm.trans ?_
  refine (MonoidHom.eq_iff_eq_on_generator g (G := Rˣ) (G' := R'ˣ) _ _).trans ?_
  simp_rw [← coe_equivToUnitHom, Units.ext_iff]

end General

section Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- If `χ` is of odd order, then `χ(-1) = 1` -/
lemma val_neg_one_eq_one_of_odd {χ : MulChar R R'} {n : ℕ} (hn : Odd n) (hχ : χ ^ n = 1) :
    χ (-1) = 1 := by
  rw [← hn.neg_one_pow, map_pow, ← χ.pow_apply' (Nat.ne_of_odd_add hn), hχ]
  exact MulChar.one_apply_coe (-1)

/-- Define the conjugation of a multiplicative character by conjugating pointwise. -/
@[simps]
def starComp [StarRing R'] (χ : MulChar R R') : MulChar R R' :=
  { (starRingEnd R').toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a ↦ (starRingEnd R') (χ a)
    map_nonunit' := by
      intro a ha
      simpa only [show χ a = 0 from χ.map_nonunit' a ha]
        using RingHom.map_zero (starRingEnd R')
  }

variable [Fintype R] [DecidableEq R]

/-- The values of a multiplicative character on `R` are `n`th roots of unity, where `n = #Rˣ`. -/
lemma val_mem_rootsOfUnity (a : Rˣ) {χ : MulChar R R'} :
    (χ.map_unit a).unit ∈ rootsOfUnity (Fintype.card Rˣ).toPNat' R' := by
  refine (mem_rootsOfUnity _ _).mpr ?_
  simp only [Nat.toPNat'_coe, Fintype.card_pos, ↓reduceIte, Units.ext_iff]
  norm_cast
  have h : (χ.map_unit a).unit = (equivToUnitHom χ) a := Units.ext rfl
  rw [h, ← map_pow, ← (equivToUnitHom χ).map_one]
  congr
  exact pow_card_eq_one

/-- The conjugate of a multiplicative character with values in `ℂ` is its inverse. -/
lemma starComp_eq_inv (χ : MulChar R ℂ) : χ.starComp = χ⁻¹ := by
  ext1 a
  simp only [starComp_apply, inv_apply_eq_inv']
  have H := Complex.norm_eq_one_of_mem_rootOfUnity <| χ.val_mem_rootsOfUnity a
  exact (Complex.inv_eq_conj H).symm

lemma starComp_apply' (χ : MulChar R ℂ) (a : R) : (starRingEnd ℂ) (χ a) = χ⁻¹ a := by
  rw [← starComp_eq_inv]
  rfl

end Ring

section IsCyclic

/-!
### Multiplicative characters on finite monoids with cyclic unit group
-/

variable {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
variable {R : Type*} [CommMonoidWithZero R]

/-- A multiplicative character on a finite commutative monoid has finite (= positive) order. -/
lemma orderOf_pos (χ : MulChar M R) : 0 < orderOf χ := by
  let e := MulChar.mulEquivToUnitHom (R := M) (R' := R)
  let χ' := e χ
  have : orderOf χ = orderOf χ' := (MulEquiv.orderOf_eq e χ).symm
  rw [this]
  have : orderOf χ' ∣ Fintype.card Mˣ := by
    refine orderOf_dvd_of_pow_eq_one ?_
    ext x
    norm_cast
    change (χ' x) ^ _ = _
    rw [← map_pow]
    simp only [pow_card_eq_one, map_one, MonoidHom.one_apply]
  exact Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero Fintype.card_ne_zero this

variable (M) in
/-- The order of the unit group of a finite monoid as a `PNat`. -/
abbrev Monoid.orderUnits : ℕ+ := ⟨Fintype.card Mˣ, Fintype.card_pos⟩

/-- If `χ` is a multiplicative character on a finite commutative monoid `M`, then `χ^#Mˣ = 1`. -/
protected
lemma pow_card_eq_one (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
  ext1 x
  rw [pow_apply_coe, ← map_pow, one_apply_coe]
  norm_cast
  rw [pow_card_eq_one, Units.val_eq_one.mpr rfl, map_one]

variable [inst_cyc : IsCyclic Mˣ]

/-- Given a finite monoid `M` with unit group `Mˣ` cyclic of order `n` and an `n`th root of
unity `ζ` in `R`, there is a multiplicative character `M → R` that sends a given generator
of `Mˣ` to `ζ`. -/
noncomputable def ofRootOfUnity {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Monoid.orderUnits M) R)
    (g : Group.Generator Mˣ) :
    MulChar M R := by
  have : orderOf ζ ∣ (Monoid.orderUnits M) :=
    orderOf_dvd_iff_pow_eq_one.mpr <| (mem_rootsOfUnity _ ζ).mp hζ
  refine ofUnitHom <| Group.Generator.monoidHom (g := g) <| this.trans <| dvd_of_eq ?_
  rw [g.orderOf_eq_natCard, Nat.card_eq_fintype_card]
  rfl

lemma ofRootOfUnity_spec {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Monoid.orderUnits M) R)
    (g : Group.Generator Mˣ) :
    ofRootOfUnity hζ g g.val = ζ := by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe]
  rw [Group.Generator.monoidHom_apply_gen]

variable (M R) in
/-- The group of multiplicative characters on a finite monoid `M` with cyclic unit group `Mˣ`
of order `n` is isomorphic to the group of `n`th roots of unity in the target `R`. -/
noncomputable def equiv_rootsOfUnity :
    MulChar M R ≃* rootsOfUnity (Monoid.orderUnits M) R where
      toFun χ :=
        ⟨χ.toUnitHom <| (IsCyclic.generator inst_cyc).val, by
          simp only [toUnitHom_eq, mem_rootsOfUnity, PNat.mk_coe, ← map_pow, pow_card_eq_one,
            map_one]⟩
      invFun ζ := ofRootOfUnity ζ.prop <| (IsCyclic.generator inst_cyc)
      left_inv χ := by
        simp only [toUnitHom_eq, eq_iff <| (IsCyclic.generator inst_cyc), ofRootOfUnity_spec]
        rfl
      right_inv ζ := by
        ext
        simp only [toUnitHom_eq, coe_equivToUnitHom, ofRootOfUnity_spec]
      map_mul' x y := by
        simp only [toUnitHom_eq, equivToUnitHom_mul_apply, Submonoid.mk_mul_mk]

end IsCyclic

section FiniteField

/-!
### Multiplicative characters on finite fields
-/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R]

/-- There is a character of order `n` on `F` if `#F ≡ 1 mod n` and the target contains
a primitive `n`th root of unity. -/
lemma exists_mulChar_orderOf {n : ℕ} (h : n ∣ Fintype.card F - 1) [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ χ : MulChar F R, orderOf χ = n := by
  have hn₀ : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn ↦ ?_
    simp only [hn, zero_dvd_iff, Nat.sub_eq_zero_iff_le] at h
    exact (Fintype.one_lt_card.trans_le h).false
  let e := MulChar.equiv_rootsOfUnity F R
  let ζ' : Rˣ := (hζ.isUnit hn₀).unit
  have h' : ζ' ^ (Monoid.orderUnits F : ℕ) = 1 := by
    have hn : n ∣ Monoid.orderUnits F := by
      rwa [Monoid.orderUnits, PNat.mk_coe, Fintype.card_units]
    ext
    push_cast
    exact (IsPrimitiveRoot.pow_eq_one_iff_dvd hζ ↑(Monoid.orderUnits F)).mpr hn
  use e.symm ⟨ζ', (mem_rootsOfUnity (Monoid.orderUnits F) ζ').mpr h'⟩
  rw [e.symm.orderOf_eq, orderOf_eq_iff hn₀]
  refine ⟨?_, fun m hm hm₀ h ↦ ?_⟩
  · ext
    push_cast
    exact hζ.pow_eq_one
  · rw [Subtype.ext_iff, Units.ext_iff] at h
    push_cast at h
    exact ((Nat.le_of_dvd hm₀ <| hζ.dvd_of_pow_eq_one _ h).trans_lt hm).false

/-- If there is a multiplicative character of order `n` on `F`, then `#F ≡ 1 mod n`. -/
lemma dvd_card_sub_one (χ : MulChar F R) : orderOf χ ∣ Fintype.card F - 1 := by
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one

/-- There is always a character on `F` of order `#F-1` with values in a ring that has
a primitive `(#F-1)`th root of unity. -/
lemma exists_mulChar_orderOf_eq [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ (Monoid.orderUnits F)) :
    ∃ χ : MulChar F R, orderOf χ = Fintype.card Fˣ :=
  exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ

variable {F}

/-- If a multiplicative character `χ` has order `n`, then all powers `χ^m` with `0 < m < n`
are nontrivial. -/
lemma isNontrivial_pow_of_lt (χ : MulChar F R) :
    ∀ m ∈ Finset.Ico 1 (orderOf χ), (χ ^ m).IsNontrivial := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  obtain ⟨hm₁, hmn⟩ := hm
  rw [MulChar.isNontrivial_iff]
  exact ((orderOf_eq_iff <| (zero_lt_one.trans_le hm₁).trans hmn).mp rfl).2 _ hmn hm₁

/- The non-zero values of a multiplicative character of order `n` are `n`th roots of unity -/
lemma val_mem_rootsOfUnity_orderOf (χ : MulChar F R) {a : F} (ha : a ≠ 0) :
    ∃ ζ : rootsOfUnity ⟨orderOf χ, χ.orderOf_pos⟩ R, ζ.val = χ a := by
  have hu : IsUnit (χ a) := ha.isUnit.map χ
  have Hu : hu.unit ∈ rootsOfUnity ⟨orderOf χ, χ.orderOf_pos⟩ R := by
    simp only [mem_rootsOfUnity, PNat.mk_coe]
    ext
    push_cast
    rw [IsUnit.unit_spec, ← χ.pow_apply' χ.orderOf_pos.ne', pow_orderOf_eq_one,
      show a = (isUnit_iff_ne_zero.mpr ha).unit by simp only [IsUnit.unit_spec],
      MulChar.one_apply_coe]
  use {val := hu.unit, property := Hu}
  simp only [IsUnit.unit_spec]

/-- The non-zero values of a multiplicative character `χ` such that `χ^n = 1`
are `n`th roots of unity -/
lemma val_mem_rootsOfUnity_of_pow_eq_one {χ : MulChar F R} {n : ℕ} (hn : n ≠ 0) (hχ : χ ^ n = 1)
    {a : F} (ha : a ≠ 0) :
    ∃ ζ : rootsOfUnity ⟨n, Nat.pos_of_ne_zero hn⟩ R, ζ.val = χ a := by
  obtain ⟨μ, hμ⟩ := χ.val_mem_rootsOfUnity_orderOf ha
  have hχ' : PNat.val ⟨orderOf χ, χ.orderOf_pos⟩ ∣ PNat.val ⟨n, Nat.pos_of_ne_zero hn⟩ :=
    orderOf_dvd_of_pow_eq_one hχ
  use ⟨μ, rootsOfUnity_le_of_dvd (PNat.dvd_iff.mpr hχ') μ.prop⟩

-- Results involving primitive roots of unity require `R` to be an integral domain.
variable [IsDomain R]

/-- If `χ` is a multiplicative character with `χ^n = 1` and `μ` is a primitive `n`th root
of unity, then, for `a ≠ 0`, there is some `k` such that `χ a = μ^k`. -/
lemma exists_val_eq_pow {χ : MulChar F R} {n : ℕ} (hn : n ≠ 0) (hχ : χ ^ n = 1) {μ : R}
    (hμ : IsPrimitiveRoot μ n) {a : F} (ha : a ≠ 0) :
    ∃ k < n, χ a = μ ^ k := by
  have hn' := Nat.pos_of_ne_zero hn
  obtain ⟨ζ, hζ⟩ := val_mem_rootsOfUnity_of_pow_eq_one hn hχ ha
  have hζ' : ζ.val.val ^ n = 1 := by
    conv => enter [1, 2]; rw [show n = PNat.val ⟨n, hn'⟩ from rfl]
    exact (mem_rootsOfUnity' (M := R) ⟨n, hn'⟩ ↑ζ).mp ζ.prop
  obtain ⟨k, hk₁, hk₂⟩ := hμ.eq_pow_of_pow_eq_one hζ' hn'
  exact ⟨k, hk₁, (hζ ▸ hk₂).symm⟩

/-- The values of a multiplicative character of order `n` are contained in `ℤ[μ]` when
`μ` is a primitive `n`th root of unity. -/
lemma val_mem_algebraAdjoin_of_pow_eq_one {χ : MulChar F R} {n : ℕ} (hn : n ≠ 0) (hχ : χ ^ n = 1)
    {μ : R} (hμ : IsPrimitiveRoot μ n) (a : F) :
    χ a ∈ Algebra.adjoin ℤ {μ} := by
  by_cases h : a = 0
  · rw [h, χ.map_zero]
    exact Subalgebra.zero_mem _
  · obtain ⟨ζ, hζ⟩ := val_mem_rootsOfUnity_of_pow_eq_one hn hχ h
    rw [← hζ]
    have μ_to : ζ.val ∈ rootsOfUnity _ R := SetLike.coe_mem ζ
    rw [mem_rootsOfUnity] at μ_to
    apply_fun ((↑) : Rˣ → R) at μ_to
    push_cast at μ_to
    obtain ⟨k, _, hk⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hμ μ_to (Nat.pos_of_ne_zero hn)
    rw [← hk]
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) k

/-- The values of a multiplicative character of order `n` are contained in `ℤ[μ]` when
`μ` is a primitive `n`th root of unity. -/
lemma val_mem_algebraAdjoin {χ : MulChar F R} {μ : R} (hμ : IsPrimitiveRoot μ (orderOf χ))
    (a : F) :
    χ a ∈ Algebra.adjoin ℤ {μ} :=
  val_mem_algebraAdjoin_of_pow_eq_one χ.orderOf_pos.ne' (pow_orderOf_eq_one χ) hμ a

/-- The Gauss sum of a nontrivial character on a finite field does not vanish. -/
lemma _root_.gaussSum_ne_zero_of_nontrivial (h : (Fintype.card F : R) ≠ 0) {χ : MulChar F R}
    (hχ : χ.IsNontrivial) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by
  intro H
  have := gaussSum_mul_gaussSum_eq_card hχ hψ
  simp only [H, zero_mul] at this
  exact h this.symm

end FiniteField

end MulChar
