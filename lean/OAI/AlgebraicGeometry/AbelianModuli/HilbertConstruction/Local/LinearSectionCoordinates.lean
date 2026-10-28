import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionCoefficientValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionCoefficientTransform
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveFractionCoordinates

/-! # Linear Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LinearSectionCoordinates

noncomputable section

/-! On every pulled-back frame, the transformed section family has
exactly the transformed polynomial coordinates of the associated graded
linear map. This is the local identity needed for projective action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R] {M : X.Modules} {n : ℕ}
variable (f : Y ⟶ X) (c : R →+* Γ(X, ⊤))
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (T : (Fin (n + 1) →₀ R) →ₗ[R] (Fin (n + 1) →₀ R))
variable (i : Fin (n + 1)) [IsIso (Ample.LineBundles.pullbackSection f (s i))]

theorem transformedSection_frameCoordinate (j : Fin (n + 1)) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (s i)) (Ample.LineBundles.pullbackSection f (Section.CoefficientTransformations.transformSectionFamily c M s T j)) =
      GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap T) (f.appTop.hom.comp c)
        (fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (s i)) (Ample.LineBundles.pullbackSection f (s k))) j := by
  have h := Pullback.SectionCoefficientTransform.coefficientSectionCombination_pullback f M c s (T (Finsupp.single j 1))
  change Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (s i))
    (Ample.LineBundles.pullbackSection f (Section.CoefficientTransformations.coefficientSectionCombination c M s (T (Finsupp.single j 1)))) = _
  rw [h]
  rw [Framed.SectionCoefficientValues.frameCoordinate_coefficientCombination]
  exact (Linear.ProjectiveFractionCoordinates.gradedLinearCoordinateValues_eq T (f.appTop.hom.comp c)
    (fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (s i)) (Ample.LineBundles.pullbackSection f (s k))) j).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LinearSectionCoordinates
