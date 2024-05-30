import JacobiSum.Auxiliary

/-!
### Auxiliary results on additive characters
-/

namespace AddChar

lemma val_isUnit {R R'} [AddGroup R] [Monoid R'] (φ : AddChar R R') (a : R) : IsUnit (φ a) :=
  IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

variable {R R' R'' : Type*} [CommRing R] [CommMonoid R'] [CommMonoid R'']

/-- The composition of a primitive additive character with an injective ring homomorphism
is also primitive. -/
lemma isPrimitive_homComp_of_isPrimitive {φ : AddChar R R'} {f : R' →* R''} (hφ : φ.IsPrimitive)
    (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := by
  intro a a_ne_zero
  obtain ⟨r, ne_one⟩ := hφ a a_ne_zero
  rw [mulShift_apply] at ne_one
  simp only [IsNontrivial, mulShift_apply, f.coe_compAddChar, Function.comp_apply]
  exact ⟨r, fun H ↦ ne_one <| hf <| f.map_one ▸ H⟩

lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit ∈ rootsOfUnity (ringChar R).toPNat' R' := by
  simp only [mem_rootsOfUnity, Nat.toPNat'_coe, h, ↓reduceIte, Units.ext_iff, CharP.cast_eq_zero,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_nsmul_pow, nsmul_eq_mul, zero_mul,
    map_zero_one, Units.val_one]

/-!
### Complex-valued additive characters
-/

section Ring

variable {R : Type*} [CommRing R]

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

end Ring

section Field

variable (F : Type*) [Field F] [Finite F] [DecidableEq F]

private lemma ringChar_ne : ringChar ℂ ≠ ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

/--  A primitive additive character on the finite field `F` with values in `ℂ`. -/
noncomputable def FiniteField.primChar_to_Complex : AddChar F ℂ := by
  refine MonoidHom.compAddChar ?_ (primitiveCharFiniteField F ℂ <| ringChar_ne F).char
  exact (IsCyclotomicExtension.algEquiv ?n ℂ (CyclotomicField ?n ℂ) ℂ : CyclotomicField ?n ℂ →* ℂ)

lemma FiniteField.primChar_to_Complex_isPrimitive : (primChar_to_Complex F).IsPrimitive := by
  refine isPrimitive_homComp_of_isPrimitive (PrimitiveAddChar.prim _) ?_
  let nn := (primitiveCharFiniteField F ℂ <| ringChar_ne F).n
  exact (IsCyclotomicExtension.algEquiv nn ℂ (CyclotomicField nn ℂ) ℂ).injective

end Field
