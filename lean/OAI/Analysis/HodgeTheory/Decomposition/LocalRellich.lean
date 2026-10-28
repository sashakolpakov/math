import OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding
import OAI.Analysis.HodgeTheory.Decomposition.RellichEnergy
import OAI.Analysis.HodgeTheory.Decomposition.CompactTransfer
import OAI.Analysis.HodgeTheory.Decomposition.SupportedLpDifference
import OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain

/-! # Local Rellich -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalRellich.Constructions

noncomputable section

/-! Actual local Rellich compactness: smooth manifold forms supported in a
sufficiently small chart and bounded in the Hodge graph norm have compact L² closure. -/

open _root_.MeasureTheory LineDeriv _root_.Metric Set
open scoped SchwartzMap BigOperators

theorem schwartz_toLp_norm_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (f : 𝓢(E, F)) : ‖f.toLp 2 volume‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  CoordinateLp.Constructions.memLp_toLp_norm_sq (f : E → F) (f.memLp 2 volume)

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projectiveManifold_local_rellich
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (K : Set V.analyticSpace), IsCompact K → K ⊆ e.source →
        MeasureVolume.Constructions.chartCoordinateForward V e '' K ⊆ closedBall z r →
        ∀ (R : ℝ), 0 ≤ R →
          IsCompact (closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) ''
            {a | (∀ x, x ∉ K → a x = 0) ∧ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ R})) := by
  obtain ⟨r, hr, hchart, hlocal⟩ := ManifoldGarding.Constructions.projectiveManifold_local_garding V e he n z hz
  refine ⟨r, hr, hchart, fun K hK hKe hKball R hR => ?_⟩
  obtain ⟨C, hC, hgrad⟩ := hlocal K hK hKe hKball
  obtain ⟨B, hB, hnorm⟩ := ManifoldGarding.Constructions.supportedEuclideanCoefficients_integral_bound V e he (n + 1) hK hKe
  let S : Set (DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :=
    {a | (∀ x, x ∉ K → a x = 0) ∧ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ R}
  let u : S → 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :=
    fun a => SupportedSchwartz.Constructions.supportedCoordinatesSchwartz V e he (n + 1) hK hKe a.val a.property.1
  let f := fun a : S => (u a).toLp 2 volume
  let g := fun a : S => Form.Constructions.smoothToProjectiveL2 V (n + 1) a.val
  let Q := Real.sqrt (B + C) * R
  have hQ : 0 ≤ Q := mul_nonneg (Real.sqrt_nonneg _) hR
  have hQs : Q ^ 2 = (B + C) * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (add_pos hB hC).le]
  have henergy (a : S) : ‖(u a).toLp 2 volume‖ ^ 2 +
      (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
        ‖(∂_{stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i} (u a)).toLp 2 volume‖ ^ 2) ≤ Q ^ 2 := by
    have ha := a.property.1
    have hg : ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a.val‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).mpr a.property.2
    have hn := (hnorm a.val ha).trans (mul_le_mul_of_nonneg_left
      ((EnergyDomain.Constructions.projectiveGraphEmbedding_value_norm_sq_le V n a.val).trans hg) hB.le)
    have hd := hgrad a.val ha
    rw [← EnergyDomain.Constructions.projectiveGraphEmbedding_norm_sq] at hd
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hg hC.le)
    simp_rw [schwartz_toLp_norm_sq, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hQs]
    change (∫ x, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) a.val.val x‖ ^ 2) +
      (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V, ∫ x,
        ‖fderiv ℝ (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) a.val.val) x
          (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)‖ ^ 2) ≤ _
    exact (add_le_add hn hd').trans_eq (add_mul B C (R ^ 2)).symm
  have hcompact := RellichEnergy.Constructions.schwartz_vector_rellich_energy
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (EuclideanSpace.basisFun (Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) ℂ)
    (SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe) Q hQ
  have hf : TotallyBounded (f '' Set.univ) := by
    apply hcompact.totallyBounded.subset
    rintro _ ⟨a, _, rfl⟩
    apply subset_closure
    refine ⟨u a, ⟨?_, henergy a⟩, rfl⟩
    exact SupportedCoordinates.Constructions.supportedEuclideanCoefficients_support V e (n + 1) a.val.val a.property.1
  obtain ⟨D, hD, hdist⟩ := SupportedLpDifference.Constructions.supportedCoordinatesLp_dist_comparison V e he (n + 1) hK hKe
  have hg : TotallyBounded (g '' Set.univ) := CompactTransfer.Constructions.totallyBounded_image_of_dist_le f g Set.univ D hD
    (fun a _ b _ => hdist a.val b.val a.property.1 b.property.1) hf
  have heq : g '' Set.univ = (Form.Constructions.smoothToProjectiveL2 V (n + 1)) '' S := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  rw [heq] at hg
  exact hg.closure.isCompact_of_isClosed isClosed_closure

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalRellich.Constructions
