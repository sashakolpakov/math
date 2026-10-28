import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM

/-! # Descent Chart Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DescentChartFormula.CM

noncomputable section

/-! ThetaCycle: the literal chart expression of a descended form, computed
through an actual smooth local section of the covering. -/

open Set
open scoped _root_.Manifold ContDiff

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

theorem descended_form_chart_formula
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (s : N → M) (U : Set N) (hU : IsOpen U)
    (hs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ s U) (hfs : ∀ y ∈ U, f (s y) = y)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) (b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n)
    (hab : b.pullback (E := E) f = a)
    (c : OpenPartialHomeomorph N F) (d : OpenPartialHomeomorph M E)
    (hc : c ∈ atlas F N) (hd : d ∈ atlas E M)
    (x : F) (hx : x ∈ c.target) (hxU : c.symm x ∈ U) (hxd : s (c.symm x) ∈ d.source) :
    b.inChart c x = (a.inChart d (d (s (c.symm x)))).compContinuousLinearMap
      (fderiv ℝ (d ∘ s ∘ c.symm) x) := by
  have hlocal : a.pullback s (c.symm x) = b (c.symm x) := by
    rw [← hab]
    exact CoverLocalM.CM.raw_pullback_local_section f hf s U hU hs hfs n b (c.symm x) hxU
  have heq : b.inChart c x = (a.pullback s).inChart c x := by
    exact congrArg (fun v => v.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c x)) hlocal.symm
  have hsAt := ((hs (c.symm x) hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  exact heq.trans (a.pullback_inChart s c d hc hd hx hxd hsAt)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DescentChartFormula.CM
