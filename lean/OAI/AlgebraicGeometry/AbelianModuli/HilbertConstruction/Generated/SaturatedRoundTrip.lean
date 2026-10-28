import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.SaturatedRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction

/-! # Saturated Round Trip -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The generated finite coordinates and saturated flat Hilbert ideals are inverse constructions over noetherian coefficient rings. -/

open _root_.AlgebraicGeometry

universe u v

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.ext_quotients {R : Type u} [CommRing R] {σ : Type v}
    {B : ℕ} {r : ℕ → ℕ} (D E : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r)
    (h : ∀ d, D.quotient d = E.quotient d) : D = E := by
  have he := funext h
  cases D
  cases E
  cases he
  rfl

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem Generated.SaturatedRoundTrip.generatedSaturatedHilbertIdeal_generatedData (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) :
    SaturatedFlatIdeals.generatedSaturatedHilbertIdeal (I.generatedData N hN B) hflat htest hr = I := by
  apply SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.ext
  exact Uniform.GeneratedReconstruction.uniformGeneratedTruncation_saturation I.ideal I.saturated P I.hilbert N hN B
    ((Nat.le_add_right N _).trans hflat)

theorem Generated.SaturatedRoundTrip.generatedData_generatedSaturatedHilbertIdeal
    (D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N}) :
    (SaturatedFlatIdeals.generatedSaturatedHilbertIdeal D hflat htest hr).generatedData N hN B = D := by
  let I := SaturatedFlatIdeals.generatedSaturatedHilbertIdeal D hflat htest hr
  apply Subtype.ext
  apply Truncated.GradedClassification.TruncatedGradedQuotientData.ext_quotients
  intro d
  apply Module.Grassmannian.ext
  change Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I.ideal N) d = (D.val.quotient d).toSubmodule
  by_cases hd : d.val < N
  · rw [DegreeGeneratedRelations.degreeGeneratedIdeal_relations_below I.ideal N d hd, D.property.1 d hd]
  · have hdN : N ≤ d.val := by omega
    have he : Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I.ideal N) d =
        Homogeneous.IdealIncidence.homogeneousDegreeRelations I.ideal d :=
      HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I.ideal I.saturated P I.hilbert N hN d hdN
    have hPD : ∀ p : PrimeSpectrum R,
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
          (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) D.val.generatedIdeal)).toIdeal P := by
      intro p
      apply (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).mpr
      exact D.val.generated_fieldHilbertPolynomial D.property ((Nat.le_add_right N _).trans hflat)
        htest hr p.asIdeal.ResidueField
    exact he.trans (D.val.generated_saturated_retained_relations D.property hflat hN hPD d hdN).symm

def Generated.SaturatedRoundTrip.saturatedHilbertGeneratedDataEquiv : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P ≃
    {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N} where
  toFun I := I.generatedData N hN B
  invFun D := SaturatedFlatIdeals.generatedSaturatedHilbertIdeal D hflat htest hr
  left_inv := Generated.SaturatedRoundTrip.generatedSaturatedHilbertIdeal_generatedData hN hflat htest hr
  right_inv := Generated.SaturatedRoundTrip.generatedData_generatedSaturatedHilbertIdeal hN hflat htest hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
