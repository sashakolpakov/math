import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.RankTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.FinitePersistence

/-! # Saturated Flat Ideals -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals

noncomputable section

/-! Actual saturated homogeneous ideals defining flat projective families with a prescribed field-fiber Hilbert polynomial. -/

open _root_.AlgebraicGeometry

universe u

structure SaturatedFlatHilbertIdeal (R : Type u) [CommRing R] (n : ℕ) (P : Polynomial ℚ) where
  ideal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)
  saturated : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated ideal.toIdeal
  flat : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading ideal))
  hilbert : ∀ p : PrimeSpectrum R,
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) ideal)).toIdeal P

attribute [instance] SaturatedFlatHilbertIdeal.flat

namespace SaturatedFlatHilbertIdeal

variable {R : Type u} [CommRing R] {n : ℕ} {P : Polynomial ℚ}

@[ext]
theorem ext {I J : SaturatedFlatHilbertIdeal R n P} (h : I.ideal = J.ideal) : I = J := by
  cases I
  cases J
  cases h
  rfl

def generatedData [IsNoetherianRing R] (I : SaturatedFlatHilbertIdeal R n P)
    (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (B : ℕ) :
    {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N} :=
  ⟨(Uniform.GeneratedCoordinates.uniformGeneratedData I.ideal I.saturated P I.hilbert N hN).truncate B,
    Uniform.GeneratedCoordinates.uniformGeneratedData_truncate_condition I.ideal I.saturated P I.hilbert N hN B⟩

end SaturatedFlatHilbertIdeal

variable {R : Type u} [CommRing R] {n B N : ℕ} {P : Polynomial ℚ}

def generatedSaturatedHilbertIdeal
    (D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N})
    (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
    (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) : SaturatedFlatHilbertIdeal R n P where
  ideal := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.val.generatedIdeal
  saturated := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated D.val.generatedIdeal
  flat := by
    have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading D.val.generatedIdeal)) :=
      D.val.projectiveFamily_flat_of_generatedFromDegree N hflat D.property
    exact Projective.SaturationBaseChange.projectiveSaturation_flat D.val.generatedIdeal
  hilbert p := (Projective.SaturationBaseChange.projectiveSaturation_fieldHilbertPolynomial D.val.generatedIdeal p.asIdeal.ResidueField P).mpr
    (D.val.generated_fieldHilbertPolynomial D.property ((Nat.le_add_right N _).trans hflat)
      htest hr p.asIdeal.ResidueField)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
