import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Cauchy Local Primitive -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyLocalPrimitive

noncomputable section

/-! Actual local antiholomorphic primitives in one complex variable. -/

open _root_.MeasureTheory _root_.Complex Set _root_.Metric Filter
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_compact_smooth_complex_extension {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) {x : ℂ} (hx : x ∈ U) :
    ∃ F : ℂ → ℂ, HasCompactSupport F ∧ ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let F : ℂ → ℂ := fun y => χ y • f y
  have hc : HasCompactSupport F := χ.hasCompactSupport.smul_right
  have hs : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · have hyU : y ∈ U := hsub (by simpa only [χ.tsupport_eq] using hy)
      exact χ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hyU))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hy)] with z hz
      change χ z • f z = 0
      rw [show χ z = 0 from hz, zero_smul]
  refine ⟨F, hc, hs, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  change χ y • f y = f y
  rw [show χ y = 1 from hy, one_smul]

theorem exists_complexDbar_local_primitive {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) {x : ℂ} (hx : x ∈ U) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ CauchyPolarCalculus.complexDbar g =ᶠ[𝓝 x] f := by
  obtain ⟨F, hc, hF, heq⟩ := exists_compact_smooth_complex_extension hU hf hx
  refine ⟨CauchyKernel.cauchyTransform F, CauchyKernel.cauchyTransform_smooth hc hF, ?_⟩
  filter_upwards [heq] with y hy
  exact (CauchyPolarIntegral.complexDbar_cauchyTransform hF hc y).trans hy

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyLocalPrimitive
