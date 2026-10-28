import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionCoordinates

noncomputable section

/-!
# ThomClass: affine characters on arbitrary complex schemes evaluate the actual scheme sections

The canonical spectrum-of-sections isomorphism identifies the affine
character space with the actual analytic open, and preserves section values.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (hU : IsAffineOpen U)

/-- The canonical affine-open spectrum isomorphism, with the scalar
structure induced by the original complex structure morphism. -/
def affineSectionOverIso : SectionEvaluation.Constructions.openOver X U ≅
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :=
  Over.isoMk hU.isoSpec (by
    change hU.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.hom U)) =
        U.ι ≫ X.hom
    rw [Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.hom U hU,
      ← Category.assoc, hU.isoSpec_hom_fromSpec])

/-- Characters of the actual section algebra are exactly points of the
corresponding actual analytic open. -/
def affineSectionPointHomeomorph :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) ≃ₜ SectionEvaluation.Constructions.analyticOpen X U :=
  ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)).trans
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (affineSectionOverIso X U hU)).symm).trans
      (SectionEvaluation.Constructions.openPointHomeomorph X U)

theorem affineSectionPointHomeomorph_val
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    (affineSectionPointHomeomorph X U hU y).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) y := by
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) y ≫
      (affineSectionOverIso X U hU).inv) ≫ SectionEvaluation.Constructions.openInclusion X U =
    ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) y ≫
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  rw [Category.assoc]
  congr 1

/-- Native evaluation of an actual scheme section is ordinary character
evaluation under the canonical affine chart. -/
theorem affineSectionPointHomeomorph_evaluation
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))
    (a : Γ(X.left, U)) :
    SectionEvaluation.Constructions.sectionEvaluationOn X U a (affineSectionPointHomeomorph X U hU y) = y a := by
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation
      ((SectionEvaluation.Constructions.openPointHomeomorph X U).symm ((SectionEvaluation.Constructions.openPointHomeomorph X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (affineSectionOverIso X U hU).inv
          (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) y))))
      (U.topIso.inv a) = y a
  rw [Homeomorph.symm_apply_apply, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_affine]
  change y ((Scheme.ΓSpecIso Γ(X.left, U)).hom
    (hU.isoSpec.inv.appTop (U.topIso.inv a))) = y a
  rw [hU.isoSpec_inv_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionCoordinates
