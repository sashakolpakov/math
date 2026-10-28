import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Automorphy Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Holomorphic automorphy factors give complex smooth transition functions. -/

open _root_.Topology Filter
open scoped _root_.Manifold ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)
  (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))

include hJ

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor_contMDiffOn (i j : Φ.periodTorus) :
    ContMDiffOn 𝓘(ℂ, Φ.space) 𝓘(ℂ, ℂ) ∞ (J.transitionFactor i j)
      ((Φ.periodChart i).source ∩ (Φ.periodChart j).source) := by
  intro z hz
  have hδ := (Φ.periodChartDifference_continuousOn i j).continuousAt
    (((Φ.periodChart i).open_source.inter (Φ.periodChart j).open_source).mem_nhds hz)
  have he : ∀ᶠ w in 𝓝 z, Φ.periodChartDifference i j w = Φ.periodChartDifference i j z :=
    hδ.eventually_mem (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton _))
  have hc : ContMDiffAt 𝓘(ℂ, Φ.space) 𝓘(ℂ, Φ.space) ∞ (Φ.periodChart i) z := by
    have h := contMDiffAt_extChartAt' (I := 𝓘(ℂ, Φ.space)) (x := i) (n := ∞) hz.1
    simpa only [Φ.period_extChart] using h
  have hv := ((hJ (Φ.periodChartDifference i j z)).contMDiff.contMDiffAt).comp z hc
  apply ContMDiffAt.contMDiffWithinAt
  apply hv.congr_of_eventuallyEq
  filter_upwards [he] with w hw
  exact congrArg (fun l => J.value l (Φ.periodChart i w)) hw

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.vectorBundleCore_isContMDiff : J.vectorBundleCore.IsContMDiff 𝓘(ℂ, Φ.space) ∞ where
  contMDiffOn_coordChange i j := (J.transitionFactor_contMDiffOn hJ i j).smul contMDiffOn_const

end

end OAI.RepresentationTheory.Theta.Geometric
