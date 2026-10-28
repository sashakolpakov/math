import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Kaehler
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Affine Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineEvaluation.Kaehler

noncomputable section

/-! Exact affine coordinates for the regular-section evaluation on an analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (hU : IsAffineOpen U)

def affineOpenIso : AbelianScheme.TateComparison.FormConstants.affineComplexTest (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) ≅ Comparison.Betti.Open.AffineIsoEvaluation.openOver X U :=
  Over.isoMk hU.isoSpec.symm (by
    change hU.isoSpec.inv ≫ (U.ι ≫ X.hom) = _
    exact (Category.assoc hU.isoSpec.inv U.ι X.hom).symm.trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU).w)

theorem affineOpenIso_inclusion :
    (affineOpenIso X U hU).hom ≫ Comparison.Betti.Open.AffineIsoEvaluation.openInclusion X U =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU := by
  apply Over.OverMorphism.ext
  rfl

def affineOpenCharacter (p : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)).symm
    ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p ≫ (affineOpenIso X U hU).inv)

theorem affineOpenCharacter_point (p : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU (affineOpenCharacter X U hU p) = p.val := by
  change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)).symm
      ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p ≫ (affineOpenIso X U hU).inv)) ≫ _ = _
  rw [Equiv.apply_symm_apply, ← affineOpenIso_inclusion]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p ≫ ·)
    ((affineOpenIso X U hU).inv_hom_id_assoc (Comparison.Betti.Open.AffineIsoEvaluation.openInclusion X U))).trans ?_
  exact (Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph_val X U ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p)).symm.trans
    (congrArg Subtype.val ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).apply_symm_apply p))

theorem affineOpenCharacter_evaluation (p : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) (a : Γ(X.left, U)) :
    affineOpenCharacter X U hU p a = Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U a p := by
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let s := (Scheme.ΓSpecIso (CommRingCat.of A)).inv a
  have h := Comparison.Betti.RegularFunctions.globalEvaluation_affine A (affineOpenCharacter X U hU p) s
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A (affineOpenCharacter X U hU p) =
      (Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p ≫ (affineOpenIso X U hU).inv :=
    Equiv.apply_symm_apply _ _
  rw [he] at h
  have hs : (affineOpenIso X U hU).inv.left.appTop s = U.topIso.inv a := by
    change hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X.left, U)).inv a) = U.topIso.inv a
    rw [hU.isoSpec_hom_appTop]
    exact congrArg U.topIso.inv (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X.left, U)) a)
  change Comparison.Betti.RegularFunctions.globalEvaluation ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm p)
    ((affineOpenIso X U hU).inv.left.appTop s) = _ at h
  rw [hs] at h
  change Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U a p = affineOpenCharacter X U hU p
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) at h
  exact (h.trans (congrArg (affineOpenCharacter X U hU p)
    (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) a))).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineEvaluation.Kaehler
