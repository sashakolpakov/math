import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Open Section Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenSectionEvaluation

noncomputable section

/-! Evaluation on an actual affine open is its original section-algebra character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (hU : IsAffineOpen U)

def affineOpenToOpenOver :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) ⟶ Open.AffineIsoEvaluation.openOver X U :=
  Over.homMk hU.isoSpec.inv (by
    change hU.isoSpec.inv ≫ (U.ι ≫ X.hom) =
      Spec.map (CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.hom U))
    rw [← Category.assoc]
    exact (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.hom U hU).symm)

theorem affineOpenToOpenOver_comp :
    affineOpenToOpenOver X U hU ≫ Open.AffineIsoEvaluation.openInclusion X U =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU := by
  apply Over.OverMorphism.ext
  rfl

def affineOpenPointInOpen
    (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) : Open.AffineIsoEvaluation.analyticOpen X U :=
  Open.AffineIsoEvaluation.openPointHomeomorph X U
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (affineOpenToOpenOver X U hU) p)

theorem affineOpenPointInOpen_val
    (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    (affineOpenPointInOpen X U hU p).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU p := by
  rw [affineOpenPointInOpen, Open.AffineIsoEvaluation.openPointHomeomorph_val,
    ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, affineOpenToOpenOver_comp]
  rfl

theorem sectionEvaluationOn_affineOpen
    (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (s : Γ(X.left, U)) :
    Open.AffineIsoEvaluation.sectionEvaluationOn X U s (affineOpenPointInOpen X U hU p) = p s := by
  change RegularFunctions.globalEvaluation ((Open.AffineIsoEvaluation.openPointHomeomorph X U).symm
      (Open.AffineIsoEvaluation.openPointHomeomorph X U _)) (U.topIso.inv s) = p s
  rw [Homeomorph.symm_apply_apply]
  change RegularFunctions.globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (affineOpenToOpenOver X U hU)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) p)) _ = _
  rw [RegularFunctions.globalEvaluation_map, RegularFunctions.globalEvaluation_affine]
  change p ((Scheme.ΓSpecIso Γ(X.left, U)).hom (hU.isoSpec.inv.appTop (U.topIso.inv s))) = p s
  rw [hU.isoSpec_inv_appTop]
  change p ((Scheme.ΓSpecIso Γ(X.left, U)).hom
    ((Scheme.ΓSpecIso Γ(X.left, U)).inv (U.topIso.hom (U.topIso.inv s)))) = p s
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenSectionEvaluation
