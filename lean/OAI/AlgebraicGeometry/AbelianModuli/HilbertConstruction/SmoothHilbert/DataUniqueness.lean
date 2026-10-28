import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedGeneratingQuotient

/-! # Data Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite generated quotient data defining the same smooth Hilbert family are equal over arbitrary rings. -/

open _root_.AlgebraicGeometry

universe u

theorem Flat.ClosedFamilies.FlatClosedHilbertFamily.generatedData_unique
    {R : Type u} [CommRing R] {n B N : ℕ} {P : Polynomial ℚ}
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom]
    (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hNB : N ≤ B)
    (D E : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N})
    (hD : D.val.projectiveIdeal = F.val.ideal) (hE : E.val.projectiveIdeal = F.val.ideal) : D = E := by
  let d : Fin (B + 1) := ⟨N, Nat.lt_succ_of_le hNB⟩
  have hQex : ∃ Q' : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N d),
      Q'.toSubmodule = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations F.val.homogeneousIdeal.toIdeal d := by
    change ∃ Q' : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n N) (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N N),
      Q'.toSubmodule = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations F.val.homogeneousIdeal.toIdeal N
    rw [Uniform.GeneratedCoordinates.generatedHilbertRanks, ite_eq_right (Nat.lt_irrefl N)]
    exact F.exists_homogeneousQuotient N hN
  obtain ⟨Q', hQ'⟩ := hQex
  have hDI : HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.val.generatedIdeal = F.val.homogeneousIdeal :=
    congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf hD
  have hEI : HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation E.val.generatedIdeal = F.val.homogeneousIdeal :=
    congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf hE
  apply Subtype.ext
  apply D.val.eq_of_generating_quotient_eq E.val hNB D.property E.property
  exact (D.val.retainedQuotient_eq_of_saturated_coordinates d _ hDI Q' hQ').trans
    (E.val.retainedQuotient_eq_of_saturated_coordinates d _ hEI Q' hQ').symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
