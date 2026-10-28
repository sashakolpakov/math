import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardCech
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentGlobal

/-! # Embedded Coherent Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentCech

noncomputable section

/-! The actual Čech comparison is a quasi-isomorphism for every coherent module on a smooth integral projective closed subvariety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem embeddedCoherentCechMap_quasiIso
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    QuasiIso (Module.AnalytificationCechMap.moduleAnalytificationCechMap X M
      (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) := by
  let N := (Scheme.Modules.pushforward f.left).obj M
  let : N.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  let : N.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f.left
  let e := AdditiveCechCoverCongr.additiveCechCoverCongrIso ((Projective.ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor (n + 1)).obj N).obj
    (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq (n + 1))
  let a := Module.AnalytificationCechMap.moduleAnalytificationCechMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) N
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1))
  have hcomp : QuasiIso (a ≫ e.hom) := Projective.Coherent.Dolbeault.projectiveModuleComparisonIsomorphism_coherent n N
  have ha : QuasiIso a := quasiIso_of_comp_right a e.hom
    (hφ := quasiIso_of_isIso e.hom) (hφφ' := hcomp)
  exact Analytification.PushforwardCech.moduleAnalytificationCechMap_quasiIso_closed f M (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1)) ha

theorem embeddedCoherentCechHomologyMap_isIso
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Module.AnalytificationCechMap.moduleAnalytificationCechMap X M
      (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) q) := by
  have := embeddedCoherentCechMap_quasiIso n X f M
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentCech
