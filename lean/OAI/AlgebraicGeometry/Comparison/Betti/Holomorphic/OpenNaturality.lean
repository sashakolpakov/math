import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Holomorphic
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback

/-! # Open Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenNaturality

noncomputable section

/-! Actual algebraic holomorphic realizations commute with Zariski open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem openHolomorphicCochainMap_restrict {V U : X.left.Opens} (h : V ≤ U) :
    Algebraic.Forms.complexPullback (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) ≫
        Algebraic.Holomorphic.openHolomorphicCochainMap X V =
      Algebraic.Holomorphic.openHolomorphicCochainMap X U ≫
        HolomorphicPullback.pullbackCochainMap (Opens.inclusion (Open.SmoothForms.analyticOpen_mono X h))
          (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) (n := ∞) (Open.SmoothForms.analyticOpen_mono X h)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply HolomorphicPullback.inclusion_injective n
  exact Betti.Smooth.CochainNaturality.smoothFormMap_naturality
    (Open.AffineIsoEvaluation.sectionEvaluationOn X V) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X V)
    (Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) (Opens.inclusion (Open.SmoothForms.analyticOpen_mono X h))
    (contMDiff_inclusion (I := 𝓘(ℝ, RegularSmoothness.NativeModel X)) (n := ∞) (Open.SmoothForms.analyticOpen_mono X h))
    (fun s p => Open.AffineIsoEvaluation.sectionEvaluationOn_restrict X h s p) n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenNaturality
