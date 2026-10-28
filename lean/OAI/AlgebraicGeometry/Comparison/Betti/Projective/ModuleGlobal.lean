import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleClosure

/-! # Module Global -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleGlobal.Dolbeault

noncomputable section

/-! The projective Čech comparison identifies the original global-section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveModuleGlobalSectionsMap (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) :
    M.val.presheaf.obj (op ⊤) ⟶ ((ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj M).obj.obj (op ⊤) :=
  (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) M).app (op ⊤)

theorem projectiveModuleGlobalSectionsMap_isIso_of_comparison (n : ℕ)
    (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) (hM : ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism n M) :
    IsIso (projectiveModuleGlobalSectionsMap n M) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let U := Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n
  let F := (SheafOfModules.toSheaf.{0} (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf).obj M
  let G := (ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj M
  let α := Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M
  let u := Module.AnalytificationCechMap.moduleAnalytificationCechMap X M U
  let e := AdditiveCechCoverCongr.additiveCechCoverCongrIso G.obj (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n)
  have hE : QuasiIso e.hom := quasiIso_of_isIso e.hom
  have hU : QuasiIso (u ≫ e.hom) := hM
  let : QuasiIso u := quasiIso_of_comp_right u e.hom (hφ := hE) (hφφ' := hU)
  let g := Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap (Analytification.Base.analytificationMap X) U F G α
  let : QuasiIso g := inferInstanceAs (QuasiIso u)
  have hV : (⨆ i, (Opens.map (Analytification.Base.analytificationMap X)).obj (U i)) = ⊤ := by
    change (⨆ i, Open.AffineIsoEvaluation.analyticOpen X (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) = ⊤
    rw [show (fun i => Open.AffineIsoEvaluation.analyticOpen X (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) = Intersections.Dolbeault.projectiveStandardCover n
      from ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n]
    exact Intersections.Dolbeault.projectiveStandardCover_covers n
  exact Cech.PullbackGlobalIsomorphism.additivePullbackGlobalSectionsMap_isIso (Analytification.Base.analytificationMap X) U F G α
    (Foundations.Scheme.ProjectiveCoordinateCover.iSup_projectiveCoordinateOpen n) hV

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleGlobal.Dolbeault
