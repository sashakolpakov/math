import OAI.AlgebraicGeometry.Comparison.Betti.Closed.OpenCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Module
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact

/-! # Analytification Cech Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationCechAcyclicity

noncomputable section

/-! The original closed-immersion analytification isomorphism transfers analytic Čech acyclicity from the ambient module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem analytification_cechIntersectionsAcyclic_closed
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
    (M : X.left.Modules) {ι : Type} (U : ι → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hM : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) U
      ((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y)).obj
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
          ((Scheme.Modules.pushforward f.left).obj M)))) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (fun i => (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj (U i))
      ((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).obj
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
    (SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).obj
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
  let e := (SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y)).mapIso
    ((ClosedImmersion.Module.moduleAnalytificationClosedPushforwardIso f).app M)
  have hpush : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) U
      ((TopCat.Sheaf.pushforward AddCommGrpCat (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj F) :=
    Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) U e hM
  exact OpenCohomology.Cech.closedSource_cechIntersectionsAcyclic (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f) U F hpush

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationCechAcyclicity
