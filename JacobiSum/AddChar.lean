import JacobiSum.Auxiliary

/-!
### Auxiliary results on additive characters
-/

namespace AddChar

variable {R R' R'' : Type*} [CommRing R] [CommMonoid R'] [CommRing R'']

lemma val_isUnit (φ : AddChar R R') (a : R) : IsUnit (φ a) :=
  IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

/-- The composition of a primitive additive character with an injective ring homomorphism
is also primitive. -/
lemma isPrimitive_homComp_of_isPrimitive {φ : AddChar R R'} (f : R' →* R'') (hφ : φ.IsPrimitive)
    (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := by
  intro a a_ne_zero
  obtain ⟨r, ne_one⟩ := hφ a a_ne_zero
  rw [mulShift_apply] at ne_one
  simp only [IsNontrivial, mulShift_apply, MonoidHom.coe_compAddChar, Function.comp_apply]
  use r
  rw [← f.map_one]
  exact fun H ↦ ne_one (hf H)

lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit ∈ rootsOfUnity (ringChar R).toPNat' R' := by
  rw [mem_rootsOfUnity]
  simp only [Nat.toPNat'_coe, h, ↓reduceIte, Units.ext_iff, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, ← map_nsmul_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_one,
    Units.val_one]

/-- Post-composing an additive character to `ℂ` with complex conjugation gives the inverse
character. -/
lemma starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R ℂ} :
    (starRingEnd ℂ).compAddChar φ = φ⁻¹ := by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
  have H := Complex.norm_eq_one_of_mem_rootOfUnity <| φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

lemma starComp_apply (hR : 0 < ringChar R) {φ : AddChar R ℂ} (a : R) :
    (starRingEnd ℂ) (φ a) = φ⁻¹ a := by
  rw [← starComp_eq_inv hR]
  rfl

end AddChar

/-!
### Additive characters on finite fields
-/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

namespace FiniteField

/- /-- A generator of the multiplicative group of a finite field. -/
noncomputable def genMultiplicativeGroup : Group.Generator Fˣ :=
  (inferInstance : IsCyclic Fˣ).generator

/-- The order of the unit group of a finite field as a `PNat`. -/
abbrev orderUnits : ℕ+ :=
  ⟨Fintype.card Fˣ, Fintype.card_pos⟩ -/

lemma ringChar_complex_ne_ringChar : ringChar ℂ ≠ ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

/--  We define `primChar` to be a primitive additive character on `F` with values in `ℂ`. -/
noncomputable def primChar : AddChar F ℂ := by
  refine MonoidHom.compAddChar ?_ (AddChar.primitiveCharFiniteField F ℂ ?_).char
  · exact (IsCyclotomicExtension.algEquiv ?n ℂ (CyclotomicField ?n ℂ) ℂ :
            CyclotomicField ?n ℂ →* ℂ)
  · exact ringChar_complex_ne_ringChar F

lemma primChar_isPrimitive : (primChar F).IsPrimitive := by
  apply AddChar.isPrimitive_homComp_of_isPrimitive
  apply AddChar.PrimitiveAddChar.prim
  have h := ringChar_complex_ne_ringChar F
  let nn := AddChar.PrimitiveAddChar.n (AddChar.primitiveCharFiniteField F ℂ h)
  exact (IsCyclotomicExtension.algEquiv nn ℂ (CyclotomicField nn ℂ) ℂ).injective

end FiniteField
