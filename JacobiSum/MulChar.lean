import Mathlib.NumberTheory.GaussSum

/-!
### Auxiliary results on multiplicative characters
-/

namespace MulChar

section General

variable {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']

/-- Two multiplicative characters on a monoid whose unit group is generated by `g`
are equal if and only if they agree on `g`. -/
lemma eq_iff {g : Rˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (χ₁ χ₂ : MulChar R R') :
    χ₁ = χ₂ ↔ χ₁ g.val = χ₂ g.val := by
  refine (Equiv.apply_eq_iff_eq equivToUnitHom).symm.trans ?_
  refine (MonoidHom.eq_iff_eq_on_generator hg _ _).trans ?_
  simp_rw [← coe_equivToUnitHom, Units.ext_iff]

end General

section RingHomComp

variable {M R R' : Type*} [CommMonoid M] [CommRing R] [CommRing R']

@[simp]
lemma ringHomComp_one (f : R →+* R') : (1 : MulChar M R).ringHomComp f = 1 := by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]

lemma ringHomComp_inv {M : Type*} [CommRing M] (χ : MulChar M R) (f : R →+* R') :
    (χ.ringHomComp f)⁻¹ = χ⁻¹.ringHomComp f := by
  ext1 a
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]

lemma ringHomComp_mul (χ φ : MulChar M R) (f : R →+* R') :
    (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f := by
  ext1 a
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]

lemma ringHomComp_pow (χ : MulChar M R) (f : R →+* R') (n : ℕ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  induction n
  case zero => simp only [pow_zero, ringHomComp_one]
  case succ n ih => simp only [pow_succ, ih, ringHomComp_mul]

end RingHomComp

section Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Define the conjugation of a multiplicative character by conjugating pointwise. -/
@[simps!]
def starComp [StarRing R'] (χ : MulChar R R') : MulChar R R' :=
  χ.ringHomComp (starRingEnd R')


variable [Fintype R] [DecidableEq R]

/-- The values of a multiplicative character on `R` are `n`th roots of unity, where `n = #Rˣ`. -/
lemma val_mem_rootsOfUnity (a : Rˣ) {χ : MulChar R R'} :
    equivToUnitHom χ a ∈ rootsOfUnity ⟨Fintype.card Rˣ, Fintype.card_pos⟩ R' := by
  rw [mem_rootsOfUnity, Units.ext_iff]
  norm_cast
  rw [← map_pow, ← (equivToUnitHom χ).map_one]
  congr
  exact pow_card_eq_one

/-- The conjugate of a multiplicative character with values in `ℂ` is its inverse. -/
lemma starComp_eq_inv (χ : MulChar R ℂ) : χ.starComp = χ⁻¹ := by
  ext1 a
  simp only [starComp_apply, inv_apply_eq_inv']
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity <| χ.val_mem_rootsOfUnity a
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


variable (M) in
/-- The order of the unit group of a finite monoid as a `PNat`. -/
abbrev Monoid.orderUnits : ℕ+ := ⟨Fintype.card Mˣ, Fintype.card_pos⟩

/-- Given a finite monoid `M` with unit group `Mˣ` cyclic of order `n` and an `n`th root of
unity `ζ` in `R`, there is a multiplicative character `M → R` that sends a given generator
of `Mˣ` to `ζ`. -/
noncomputable def ofRootOfUnity {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Monoid.orderUnits M) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    MulChar M R := by
  have : orderOf ζ ∣ (Monoid.orderUnits M) :=
    orderOf_dvd_iff_pow_eq_one.mpr <| (mem_rootsOfUnity _ ζ).mp hζ
  refine ofUnitHom <| monoidHomOfForallMemZpowers hg <| this.trans <| dvd_of_eq ?_
  rw [orderOf_generator_eq_natCard hg, Nat.card_eq_fintype_card, PNat.mk_coe]

lemma ofRootOfUnity_spec {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Monoid.orderUnits M) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ofRootOfUnity hζ hg g = ζ := by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe,
    monoidHomOfForallMemZpowers_apply_gen]

variable (M R) in
/-- The group of multiplicative characters on a finite monoid `M` with cyclic unit group `Mˣ`
of order `n` is isomorphic to the group of `n`th roots of unity in the target `R`. -/
noncomputable def equiv_rootsOfUnity [inst_cyc : IsCyclic Mˣ] :
    MulChar M R ≃* rootsOfUnity (Monoid.orderUnits M) R where
      toFun χ :=
        ⟨χ.toUnitHom <| Classical.choose inst_cyc.exists_generator, by
          simp only [toUnitHom_eq, mem_rootsOfUnity, PNat.mk_coe, ← map_pow, pow_card_eq_one,
            map_one]⟩
      invFun ζ := ofRootOfUnity ζ.prop <| Classical.choose_spec inst_cyc.exists_generator
      left_inv χ := by
        simp only [toUnitHom_eq, eq_iff <| Classical.choose_spec inst_cyc.exists_generator,
          ofRootOfUnity_spec, coe_equivToUnitHom]
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
lemma orderOf_dvd_card_sub_one (χ : MulChar F R) : orderOf χ ∣ Fintype.card F - 1 := by
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one

/-- There is always a character on `F` of order `#F-1` with values in a ring that has
a primitive `(#F-1)`th root of unity. -/
lemma exists_mulChar_orderOf_eq_card_units [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ (Monoid.orderUnits F)) :
    ∃ χ : MulChar F R, orderOf χ = Fintype.card Fˣ :=
  exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ

variable {F}

/-- If a multiplicative character `χ` has order `n`, then all powers `χ^m` with `0 < m < n`
are nontrivial. -/
lemma isNontrivial_pow_of_lt (χ : MulChar F R) :
    ∀ m ∈ Finset.Ico 1 (orderOf χ), χ ^ m ≠ 1 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  obtain ⟨hm₁, hmn⟩ := hm
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
    (hχ : χ ≠ 1) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 :=
  fun H ↦ h.symm <| zero_mul (gaussSum χ⁻¹ _) ▸ H ▸ gaussSum_mul_gaussSum_eq_card hχ hψ

end FiniteField

end MulChar
