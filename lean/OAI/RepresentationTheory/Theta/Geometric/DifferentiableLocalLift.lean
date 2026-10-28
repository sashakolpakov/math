import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Differentiable Local Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferentiableLocalLift

noncomputable section

/-! A continuous lift through a map with an injective, continuously split
differential is differentiable whenever its composite is differentiable. -/

open scoped _root_.Manifold _root_.Topology
open Set

variable {V E F M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]

theorem continuousLinearMap_exists_leftInverse [CompleteSpace E] [CompleteSpace F]
    (d : E →L[ℂ] F) (hd : Function.Bijective d) :
    ∃ i : F →L[ℂ] E, Function.LeftInverse i d := by
  have hinj : d.ker = ⊥ := LinearMap.ker_eq_bot.mpr hd.1
  have hsurj : d.range = ⊤ :=
    LinearMap.range_eq_top.mpr (show Function.Surjective d.toLinearMap from hd.2)
  let e := ContinuousLinearEquiv.ofBijective d hinj hsurj
  exact ⟨e.symm.toContinuousLinearMap, e.symm_apply_apply⟩

theorem mdifferentiableAt_localLift (f : M → N) (g : V → M) (x : V)
    (f' : E →L[ℂ] F) (i : F →L[ℂ] E)
    (hf : HasMFDerivAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) f (g x) f')
    (hi : Function.LeftInverse i f') (hg : ContinuousAt g x)
    (hfg : MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, F)) (f ∘ g) x) :
    MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, E)) g x := by
  let G := writtenInExtChartAt (𝓘(ℂ, V)) (𝓘(ℂ, E)) x g
  let H := writtenInExtChartAt (𝓘(ℂ, V)) (𝓘(ℂ, F)) x (f ∘ g)
  let K := writtenInExtChartAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) (g x) f
  have hG : ContinuousAt G x := by
    have h := (continuousAt_extChartAt (I := 𝓘(ℂ, E)) (x := g x)).comp hg
    simpa [G, writtenInExtChartAt, chartAt_self_eq, extChartAt_self_eq] using h
  have hH : DifferentiableAt ℂ H x := by
    have h := hfg.differentiableWithinAt_writtenInExtChartAt
    simpa [H, extChartAt_self_eq, chartAt_self_eq, differentiableWithinAt_univ] using h
  have hK : HasFDerivAt K f' (G x) := by
    have h := hf.2
    have h' : HasFDerivAt K f' ((extChartAt (𝓘(ℂ, E)) (g x)) (g x)) := by
      exact h.hasFDerivAt (by simp)
    simpa [G, writtenInExtChartAt, chartAt_self_eq, extChartAt_self_eq] using h'
  have hcomp : K ∘ G =ᶠ[𝓝 x] H := by
    have h := writtenInExtChartAt_comp (I := 𝓘(ℂ, V)) (I' := 𝓘(ℂ, E)) (I'' := 𝓘(ℂ, F))
      (g := f) hg.continuousWithinAt (s := Set.univ)
    simpa [K, G, H, extChartAt_self_eq, chartAt_self_eq] using h.symm
  have hdiff := hK.of_comp_of_leftInverse hG hH.hasFDerivAt hcomp hi
  apply (mdifferentiableAt_iff g x).mpr
  refine ⟨hg, ?_⟩
  simpa [G, extChartAt_self_eq, chartAt_self_eq, differentiableWithinAt_univ] using hdiff.differentiableAt

end

end OAI.RepresentationTheory.Theta.Geometric.DifferentiableLocalLift
