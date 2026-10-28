import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed

/-! # Projective Variety Compactness -/

namespace OAI.AlgebraicGeometry

/-!
# Compactness of the genuine analytic points of projective complex schemes

The point carrier is the native morphism type over `Spec ℂ`, equipped with
the affine-test analytic topology. Compactness is transported through the
proved projective-space comparison and actual closed-immersion point map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- A projectively embedded complex scheme has compact analytic complex points. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.compactSpace_complexPoints (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) := by
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  let : CompactSpace
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension))) :=
    ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints_compactSpace P.ambientDimension
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    P.toOverHom).compactSpace

/-- The analytic points of a projectively embedded complex scheme are Hausdorff. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.t2Space_complexPoints (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) := by
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    P.toOverHom).isEmbedding.t2Space

/-- The analytic points of a projectively embedded complex scheme are second-countable. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.secondCountableTopology_complexPoints (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) := by
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    P.toOverHom).isEmbedding.secondCountableTopology

end

/-- No compactness field is added to a smooth projective presentation: it follows
from its actual projective embedding and the analytic point construction. -/
instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_compactSpace (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
  P.projective.compactSpace_complexPoints

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_t2Space (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
  P.projective.t2Space_complexPoints

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_secondCountableTopology (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
  P.projective.secondCountableTopology_complexPoints

end OAI.AlgebraicGeometry
