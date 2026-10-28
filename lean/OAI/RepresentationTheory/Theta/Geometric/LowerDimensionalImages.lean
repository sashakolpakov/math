import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # Lower Dimensional Images -/

namespace OAI.RepresentationTheory.Theta.Geometric.LowerDimensionalImages

noncomputable section

/-! A differentiable image from a strictly smaller dimensional space
has Haar measure zero, by extending along a linear retraction and applying
the proved equal-dimensional Jacobian theorem. -/

open Set _root_.Module _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem measure_image_eq_zero_of_finrank_lt
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [IsAddHaarMeasure μ]
    {f : V → W} {U : Set V} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hdim : finrank ℝ V < finrank ℝ W) : μ (f '' U) = 0 := by
  obtain ⟨i, hi⟩ := (finrank_le_iff_exists_linearMap (R := ℝ) (M := V) (M' := W)).mp hdim.le
  obtain ⟨q₀, hq₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let q := q₀.toContinuousLinearMap
  have hqi (v : V) : q (i v) = v := LinearMap.congr_fun hq₀ v
  let F : W → W := fun w => f (q w)
  let d : W → W →L[ℝ] W := fun w => (fderiv ℝ f (q w)).comp q
  have hd (w : W) (hw : w ∈ q ⁻¹' U) : HasFDerivWithinAt F (d w) (q ⁻¹' U) w :=
    ((hf.differentiableAt (hU.mem_nhds hw)).hasFDerivAt.comp w q.hasFDerivAt).hasFDerivWithinAt
  have hdet (w : W) (_hw : w ∈ q ⁻¹' U) : (d w).det = 0 := by
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hk
    have hdi : Function.Injective (d w) := LinearMap.ker_eq_bot.mp hk
    have hq : Function.Injective q₀ := fun a b hab => hdi (congrArg (fderiv ℝ f (q w)) hab)
    exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hq)
  have hz := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd hdet
  apply measure_mono_null (t := F '' (q ⁻¹' U)) ?_ hz
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨i v, ?_, ?_⟩
  · change q (i v) ∈ U
    rw [hqi]
    exact hv
  · change f (q (i v)) = f v
    rw [hqi]

end

end OAI.RepresentationTheory.Theta.Geometric.LowerDimensionalImages
