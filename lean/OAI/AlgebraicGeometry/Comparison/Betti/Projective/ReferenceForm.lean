import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCech
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFormsAcyclic

/-! # Reference Form -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ReferenceForm

noncomputable section

/-! Every Čech column of the original algebraic-to-holomorphic form map is a quasi-isomorphism on projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex

section

theorem algebraicHolomorphicFormCechMap_quasiIso_of_module
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    {ι : Type} (U : ι → X.left.Opens) (r : ℕ)
    (hu : QuasiIso (Module.AnalytificationCechMap.moduleAnalytificationCechMap X (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r) U)) :
    QuasiIso (ReferenceFormCech.algebraicHolomorphicFormCechMap X U r) := by
  let C := cechComplexFunctor (A := AddCommGrpCat.{0}) U
  let D := cechComplexFunctor (A := AddCommGrpCat.{0}) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
  let E₀ := C.mapIso ((TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of X.left)).mapIso
    (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X r))
  let E₁ := D.mapIso ((TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))).mapIso
    (Analytification.Term.analyticExteriorFormForgetIso X r))
  let u := Module.AnalytificationCechMap.moduleAnalytificationCechMap X (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r) U
  let φ := ReferenceFormCech.algebraicHolomorphicFormCechMap X U r
  have h : E₀.hom ≫ φ = u ≫ E₁.hom := ReferenceFormCech.algebraicHolomorphicFormCechMap_normalization X U r
  have hE₁ : QuasiIso E₁.hom := quasiIso_of_isIso E₁.hom
  have hcomp : QuasiIso (E₀.hom ≫ φ) := by
    rw [h]
    exact quasiIso_comp u E₁.hom (hφ := hu) (hφ' := hE₁)
  have hE₀ : QuasiIso E₀.hom := quasiIso_of_isIso E₀.hom
  exact quasiIso_of_comp_left E₀.hom φ (hφ := hE₀) (hφφ' := hcomp)

end

namespace Dolbeault

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveOriginalFormCechMap_quasiIso (n r : ℕ) :
    QuasiIso (ReferenceFormCech.algebraicHolomorphicFormCechMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1)))
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1)) r) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))
  let M := Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r
  let : M.IsQuasicoherent := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X r
  let : M.IsFiniteType := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_finiteType X r
  let u := Module.AnalytificationCechMap.moduleAnalytificationCechMap X M (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1))
  let e := AdditiveCechCoverCongr.additiveCechCoverCongrIso ((ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor (n + 1)).obj M).obj
    (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq (n + 1))
  have he : QuasiIso e.hom := quasiIso_of_isIso e.hom
  have hcomp : QuasiIso (u ≫ e.hom) := Coherent.Dolbeault.projectiveModuleComparisonIsomorphism_coherent n M
  have hu : QuasiIso u := quasiIso_of_comp_right u e.hom (hφ := he) (hφφ' := hcomp)
  exact algebraicHolomorphicFormCechMap_quasiIso_of_module X (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1)) r hu

end Dolbeault

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ReferenceForm
