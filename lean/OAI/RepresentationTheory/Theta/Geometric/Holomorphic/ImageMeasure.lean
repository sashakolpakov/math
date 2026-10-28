import OAI.RepresentationTheory.Theta.Geometric.LowerDimensionalImages
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Image Measure -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure

noncomputable section

/-! Strict complex dimension drop forces the image of a holomorphic
map to have zero Haar measure in its target. -/

open Set _root_.Module _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem measure_image_eq_zero_of_complex_finrank_lt
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [IsAddHaarMeasure μ]
    {f : V → W} {U : Set V} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hdim : finrank ℂ V < finrank ℂ W) : μ (f '' U) = 0 := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ ℂ V
  let : NormedSpace ℝ W := NormedSpace.restrictScalars ℝ ℂ W
  apply LowerDimensionalImages.measure_image_eq_zero_of_finrank_lt μ hU (hf.restrictScalars ℝ)
  rw [finrank_real_of_complex, finrank_real_of_complex]
  omega

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure
