import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

/-! # Differential -/

namespace OAI.LieTheory.Semisimple.Differential.Constructions.CharacterTriviality

/-! Differential support for CharacterTriviality. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

theorem vectorDerivative_comp
    {E H F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (f : M → N) (g : N → F) (x : M)
    (hg : MDifferentiableAt (𝓘(ℝ, H)) (𝓘(ℝ, F)) g (f x))
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, H)) f x) :
    mvfderiv (𝓘(ℝ, E)) (g ∘ f) x =
      (mvfderiv (𝓘(ℝ, H)) g (f x)).comp (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, H)) f x) := by
  unfold mvfderiv
  rw [mfderiv_comp x hg hf, ContinuousLinearMap.comp_assoc]
  rfl

theorem vectorDerivative_eq_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    mvfderiv (𝓘(ℝ, E)) f x = fderiv ℝ f x := by
  convert! mfderiv_eq_fderiv (𝕜 := ℝ) (f := f) (x := x)

theorem vectorDerivative_clm
    {E F F' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace M] [ChartedSpace E M]
    (A : F →L[ℝ] F') (f : M → F) (x : M)
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x) :
    mvfderiv (𝓘(ℝ, E)) (A ∘ f) x = A.comp (mvfderiv (𝓘(ℝ, E)) f x) := by
  have h := mfderiv_comp x A.differentiable.differentiableAt.mdifferentiableAt hf
  rw [mfderiv_eq_fderiv, A.fderiv] at h
  convert! h

/-- Supply the smoothness instance hidden by the irreducible `minSmoothness`. -/
instance realLieGroupMinSmoothness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (𝓘(ℝ, E)) ∞ G] :
    LieGroup (𝓘(ℝ, E)) (minSmoothness ℝ 3) G := by
  rw [minSmoothness_of_isRCLikeNormedField]
  infer_instance

variable {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem locallyConstant_of_mfderiv_zero
    {f : M → F} (hf : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f)
    (hd : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x = 0) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  let e := extChartAt (𝓘(ℝ, E)) x
  have he : IsOpen e.target := isOpen_extChartAt_target x
  have hx : e x ∈ e.target := mem_extChartAt_target x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp he (e x) hx
  have hc (y : E) (hy : y ∈ e.target) :
      MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) e.symm y := by
    have h := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, E)) (n := ∞) x hy
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, mdifferentiableWithinAt_univ] using
      h.mdifferentiableWithinAt (by simp)
  have hf' : DifferentiableOn ℝ (f ∘ e.symm) (Metric.ball (e x) r) := by
    intro y hy
    exact ((hf (e.symm y)).comp y (hc y (hball hy))).differentiableAt.differentiableWithinAt
  have hd' : ∀ y ∈ Metric.ball (e x) r, fderiv ℝ (f ∘ e.symm) y = 0 := by
    intro y hy
    rw [← mfderiv_eq_fderiv, mfderiv_comp y (hf (e.symm y)) (hc y (hball hy)), hd]
    rfl
  have hn : e.source ∩ e ⁻¹' Metric.ball (e x) r ∈ 𝓝 x := by
    apply inter_mem (extChartAt_source_mem_nhds x)
    exact (continuousAt_extChartAt (I := 𝓘(ℝ, E)) x).preimage_mem_nhds
      (Metric.ball_mem_nhds (e x) hr)
  filter_upwards [hn] with y hy
  have hconst := Metric.isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball (e x) r).isPreconnected hf' hd' hy.2 (Metric.mem_ball_self hr)
  simpa only [Function.comp_apply, e.left_inv hy.1,
    e.left_inv (mem_extChartAt_source x)] using hconst

theorem eq_of_mfderiv_zero [PreconnectedSpace M]
    {f : M → F} (hf : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f)
    (hd : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x = 0)
    (x y : M) : f x = f y :=
  (locallyConstant_of_mfderiv_zero hf hd).apply_eq_of_preconnectedSpace x y

end OAI.LieTheory.Semisimple.Differential.Constructions.CharacterTriviality
