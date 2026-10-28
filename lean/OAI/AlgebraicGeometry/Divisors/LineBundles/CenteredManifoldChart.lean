import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic

/-! # Centered Manifold Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CenteredManifoldChart.BundleCycles

noncomputable section

/-! Actual manifold charts centered at the given point, with their
two-sided differentiability derived from the atlas and translation. -/

open scoped _root_.Manifold ContDiff

variable (F B : Type) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ, F) ω B]

def centeredManifoldChart (b : B) : OpenPartialHomeomorph B F :=
  (chartAt F b).transHomeomorph (Homeomorph.subRight (chartAt F b b))

omit [NormedSpace ℂ F] [IsManifold 𝓘(ℂ, F) ω B] in
theorem centeredManifoldChart_source (b : B) : b ∈ (centeredManifoldChart F B b).source :=
  mem_chart_source F b

omit [NormedSpace ℂ F] [IsManifold 𝓘(ℂ, F) ω B] in
theorem centeredManifoldChart_point (b : B) : centeredManifoldChart F B b b = 0 :=
  sub_self _

theorem centeredManifoldChart_mdifferentiable (b : B) :
    (centeredManifoldChart F B b).MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, F) := by
  have ht : (Homeomorph.subRight (chartAt F b b)).toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ, F) 𝓘(ℂ, F) := by
    constructor
    · exact (show ContDiff ℂ 1 (fun z : F => z - chartAt F b b) from
        contDiff_id.sub contDiff_const).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
    · exact (show ContDiff ℂ 1 (fun z : F => z + chartAt F b b) from
        contDiff_id.add contDiff_const).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
  unfold centeredManifoldChart
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (mdifferentiable_chart (I := 𝓘(ℂ, F)) b).trans ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CenteredManifoldChart.BundleCycles
