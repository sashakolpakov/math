import OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentCech

/-! # Embedded Coherent Analytic Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentAnalyticAcyclicity

noncomputable section

/-! Coherent analytifications on every smooth integral projective closed subvariety are acyclic on the actual induced coordinate intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem embeddedCoherent_analyticCechIntersectionsAcyclic
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion f.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
      ((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).obj
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)) := by
  let Y := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let N := (Scheme.Modules.pushforward f.left).obj M
  let : N.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  let : N.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f.left
  have hN := Projective.Coherent.Dolbeault.projectiveAnalyticCechAcyclic_coherent n N
  change SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (Projective.Intersections.Dolbeault.projectiveStandardCover n)
    ((Projective.ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj N) at hN
  rw [← ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n] at hN
  have h := Closed.AnalytificationCechAcyclicity.analytification_cechIntersectionsAcyclic_closed f M
    (fun i => Open.AffineIsoEvaluation.analyticOpen Y (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) hN
  have hcover : (fun i => (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj
      (Open.AffineIsoEvaluation.analyticOpen Y (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))) =
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :=
    funext (fun i => Holomorphic.ModulePushforwardSquare.analyticSchemePreimageOpen_analyticOpen f (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
  exact hcover ▸ h

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentAnalyticAcyclicity
