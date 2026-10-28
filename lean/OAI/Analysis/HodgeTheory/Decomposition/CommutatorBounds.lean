import OAI.Analysis.HodgeTheory.Decomposition.ManifoldCommutators
import OAI.Analysis.HodgeTheory.Decomposition.ZeroOrder
import OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport

/-! # Commutator Bounds -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CommutatorBounds.Constructions

noncomputable section

/-! The actual cutoff commutators are bounded order-zero operators in the
genuine projective L² norms. -/

open scoped _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveDCommutator_zero_off_support (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {x : V.analyticSpace} (hx : x ∉ tsupport f) : ManifoldCommutators.Constructions.projectiveDCommutator V n f hf a x = 0 := by
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a) x -
    RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) x = 0
  rw [SupportedCoordinates.Constructions.manifold_d_zero_off_closed V n _ (isClosed_tsupport f)
    (fun _ hy => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n f hf a hy) hx,
    RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V (n + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hx, sub_self]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveDeltaCommutator_zero_off_support (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {x : V.analyticSpace} (hx : x ∉ tsupport f) : ManifoldCommutators.Constructions.projectiveDeltaCommutator V n f hf a x = 0 := by
  change AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a) x -
    RealMultiplier.Constructions.projectiveRealMultiplier V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a) x = 0
  rw [CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n _ (isClosed_tsupport f)
    (fun _ hy => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V (n + 1) f hf a hy) hx,
    RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a) hx, sub_self]

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveDCommutator_L2_bound (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) (hs : tsupport f ⊆ e.source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) (ManifoldCommutators.Constructions.projectiveDCommutator V n f hf a)‖ ≤
        B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  let K := tsupport f
  have hK : IsCompact K := (isClosed_tsupport f).isCompact
  have hL := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hs
  have hLU : MeasureVolume.Constructions.chartCoordinateForward V e '' K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hs hx)
  obtain ⟨C, hC, hbound⟩ := CutoffCommutator.Constructions.firstOrderCutoffCoefficient_bounded
    (fun i _ => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun z => f (MeasureVolume.Constructions.chartCoordinateInverse V e z)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hL hLU
    (fun _ => contDiffOn_const) (RealMultiplier.Constructions.projectiveRealFunction_chart_smooth V e he f hf)
  apply ZeroOrder.Constructions.projective_supported_zeroOrder_bound V e he n (n + 1) hK hs (ManifoldCommutators.Constructions.projectiveDCommutator V n f hf)
    (fun a _ hx => projectiveDCommutator_zero_off_support V n f hf a hx) C hC
  intro a z hz
  rw [ManifoldCommutators.Constructions.projectiveDCommutator_coefficients V e he n f hf a z (hLU hz)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _))

theorem projectiveDeltaCommutator_L2_bound (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) (hs : tsupport f ⊆ e.source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      ‖Form.Constructions.smoothToProjectiveL2 V n (ManifoldCommutators.Constructions.projectiveDeltaCommutator V n f hf a)‖ ≤
        B * ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ := by
  let K := tsupport f
  have hK : IsCompact K := (isClosed_tsupport f).isCompact
  have hL := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hs
  have hLU : MeasureVolume.Constructions.chartCoordinateForward V e '' K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hs hx)
  obtain ⟨C, hC, hbound⟩ := CutoffCommutator.Constructions.firstOrderCutoffCoefficient_bounded
    (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun z => f (MeasureVolume.Constructions.chartCoordinateInverse V e z)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hL hLU
    (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he) (RealMultiplier.Constructions.projectiveRealFunction_chart_smooth V e he f hf)
  apply ZeroOrder.Constructions.projective_supported_zeroOrder_bound V e he (n + 1) n hK hs (ManifoldCommutators.Constructions.projectiveDeltaCommutator V n f hf)
    (fun a _ hx => projectiveDeltaCommutator_zero_off_support V n f hf a hx) C hC
  intro a z hz
  rw [ManifoldCommutators.Constructions.projectiveDeltaCommutator_coefficients V e he n f hf a z (hLU hz)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _))

end

end OAI.Analysis.HodgeTheory.Decomposition.CommutatorBounds.Constructions
