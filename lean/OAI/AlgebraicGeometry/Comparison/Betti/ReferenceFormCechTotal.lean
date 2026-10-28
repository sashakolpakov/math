import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveTotalColumn
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ReferenceForm
import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteCech

/-! # Reference Form Cech Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCechTotal

noncomputable section

/-! The original form comparison on projective space induces a quasi-isomorphism of Čech–de Rham total complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex₂

section

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def algebraicAdditivePresheafComplex : CochainComplex ((Opens X.left)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  (Cech.ForgetModules.modulePresheafForget.mapHomologicalComplex (.up ℕ)).obj (ConcreteCech.algebraicSheafPresheafComplex X)

def analyticHolomorphicAdditivePresheafComplex :
    CochainComplex ((Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  (Cech.ForgetModules.modulePresheafForget.mapHomologicalComplex (.up ℕ)).obj
    (Complex.SheafCechBicomplex.complexSheafPresheafComplex (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X))

def originalHolomorphicAdditivePresheafMap : algebraicAdditivePresheafComplex X ⟶
    ((AdditiveCechPullbackBicomplex.additivePresheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℕ)).obj
      (analyticHolomorphicAdditivePresheafComplex X) :=
  (Cech.ForgetModules.modulePresheafForget.mapHomologicalComplex (.up ℕ)).map
    (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).map (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))

variable {ι : Type} (U : ι → X.left.Opens)

def originalHolomorphicCechBicomplexMap :
    AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of X.left) U (algebraicAdditivePresheafComplex X) ⟶
      AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
        (analyticHolomorphicAdditivePresheafComplex X) :=
  AdditiveCechPullbackBicomplex.additiveCechPullbackBicomplexMap (Analytification.Base.analytificationMap X) U (originalHolomorphicAdditivePresheafMap X)

theorem originalHolomorphicCechBicomplexMap_f (r : ℕ) :
    (originalHolomorphicCechBicomplexMap X U).f r = ReferenceFormCech.algebraicHolomorphicFormCechMap X U r := rfl

def originalHolomorphicCechTotalMap :
    (AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of X.left) U (algebraicAdditivePresheafComplex X)).total (.up ℕ) ⟶
      (AdditiveCechPullbackBicomplex.nativeAdditiveCechBicomplex (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
        (analyticHolomorphicAdditivePresheafComplex X)).total (.up ℕ) :=
  total.map (originalHolomorphicCechBicomplexMap X U) (.up ℕ)

theorem originalHolomorphicCechTotalMap_quasiIso_of_columns
    (h : ∀ r, QuasiIso (ReferenceFormCech.algebraicHolomorphicFormCechMap X U r)) :
    QuasiIso (originalHolomorphicCechTotalMap X U) :=
  AdditiveTotalColumn.additive_total_map_quasiIso_of_columns (originalHolomorphicCechBicomplexMap X U) h

end

namespace Dolbeault

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveOriginalHolomorphicCechTotalMap_quasiIso (n : ℕ) :
    QuasiIso (originalHolomorphicCechTotalMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1)))
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1))) :=
  originalHolomorphicCechTotalMap_quasiIso_of_columns (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1)))
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1)) (Projective.ReferenceForm.Dolbeault.projectiveOriginalFormCechMap_quasiIso n)

end Dolbeault

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCechTotal
