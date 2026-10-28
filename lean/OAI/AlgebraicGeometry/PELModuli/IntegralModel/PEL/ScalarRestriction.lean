import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Scalar Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! Restriction of the coefficient ring in the actual integral PEL functor.
The geometric Lie characters are recovered from the test scheme's structure
map, so no additional signature comparison is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {R R' : Type} [CommRing R] [CommRing R']
  {iotaO : NumberField.RingOfIntegers E →+* R}
  (φ : R →+* R') (Y : Over (Spec (.of R')))

abbrev ScalarRestriction.coefficientRestriction : Over (Spec (.of R)) :=
  (Over.map (Spec.map (CommRingCat.ofHom φ))).obj Y

omit [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
/-- A geometric point over the smaller coefficient ring has its unique
coefficient character on the larger ring, obtained from the actual point. -/
theorem ScalarRestriction.geometric_point_coefficient_extension
    {F : Type} [Field F] (j : R →+* F) (p : Spec (.of F) ⟶ Y.left)
    (hp : p ≫ (ScalarRestriction.coefficientRestriction φ Y).hom = Spec.map (CommRingCat.ofHom j)) :
    ∃ j' : R' →+* F,
      p ≫ Y.hom = Spec.map (CommRingCat.ofHom j') ∧ j'.comp φ = j := by
  let j' := (Spec.preimage (p ≫ Y.hom)).hom
  have hj' : Spec.map (CommRingCat.ofHom j') = p ≫ Y.hom := Spec.map_preimage _
  refine ⟨j', hj'.symm, ?_⟩
  have hspec : Spec.map (CommRingCat.ofHom (j'.comp φ)) = Spec.map (CommRingCat.ofHom j) := by
    change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom j') = _
    rw [Spec.map_comp, hj', Category.assoc]
    exact hp
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)

/-- The same family and action are an actual PEL object over the smaller
coefficient ring, with the prescribed Lie characters proved compatible. -/
def Has.IntegralPELObject.restrictScalars
    (A : Has.IntegralPELObject P R' (φ.comp iotaO) N Y) :
    Has.IntegralPELObject P R iotaO N (ScalarRestriction.coefficientRestriction φ Y) where
  data := A.data
  rosati := A.rosati
  lieRanks := by
    intro F hF hclosed j p hp τ
    obtain ⟨j', hj', hc⟩ := ScalarRestriction.geometric_point_coefficient_extension φ Y j p hp
    have h := A.lieRanks F j' p hj' τ
    simpa only [← RingHom.comp_assoc, hc] using h

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  (iota : E →+* K) (j : K →+* L) (Z : Over (Spec (.of L)))

/-- The characteristic-zero PEL object after restriction of coefficients.
Its polarized family and integral action remain the actual given objects. -/
def ScalarRestriction.characteristicZeroPELRestrictScalars (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P (j.comp iota) N Z) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (ScalarRestriction.coefficientRestriction j Z) :=
  Has.IntegralPELObject.toCharacteristicZero
    (Has.IntegralPELObject.restrictScalars j Z
      (show Has.IntegralPELObject P L
        (j.comp (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) N Z from
        BaseChange.integralPELOfCharacteristicZero A))

@[simp] theorem ScalarRestriction.characteristicZeroPELRestrictScalars_data
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P (j.comp iota) N Z) :
    Has.characteristicZeroPELData P (ScalarRestriction.characteristicZeroPELRestrictScalars iota j Z A) =
      Has.characteristicZeroPELData P A := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
