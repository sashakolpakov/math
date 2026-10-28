import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianNonzero

/-! # Norm Gaussian Cutoffs -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianCutoffs.Construction

noncomputable section

/-! Stable one-dimensional norm Gaussians admit arbitrarily large compact
cutoffs invariant under every prescribed compact family of translations. -/

open _root_.MeasureTheory

theorem norm_hasGaussianCutoffs_of_stable
    {F E : Type} [NontriviallyNormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E]
    [FiniteDimensional F E] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (μ : Measure E) (ψ : AddChar F ℂ) (a : Fˣ) (Γ : ℂ) (R : ℝ)
    (hstable : ∀ r : ℝ, R ≤ r → UltraNormGaussian.Construction.normGaussianCutoff μ ψ (a : F) r = Γ) :
    GaussianCutoff.Construction.HasGaussianCutoffs μ ψ (fun x => (a : F) * Algebra.norm F x) Γ := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let e := QuadraticNorm.Construction.quadraticFieldCoordinates hF hEmbedding hQuadratic
  let q : Local.FunctionsMetaplectic.Construction.Position F 2 → F := fun x => (a : F) * Algebra.norm F (e.symm x)
  have hq : Continuous q := continuous_const.mul
    ((QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding).comp e.symm.continuous)
  have hp : IsProperMap q := (FieldModulus.Construction.fieldDilation a).toHomeomorph.isProperMap.comp
    ((NormHaar.Construction.quadraticNorm_isProperMap hF hEmbedding hQuadratic).comp e.symm.toHomeomorph.isProperMap)
  have hhom (b : F) (x : Local.FunctionsMetaplectic.Construction.Position F 2) : q (b • x) = b ^ 2 * q x := by
    dsimp only [q]
    rw [map_smul, Algebra.smul_def, map_mul, Algebra.norm_algebraMap, hQuadratic]
    ring
  have hzero (x : Local.FunctionsMetaplectic.Construction.Position F 2) (hx : q x = 0) : x = 0 := by
    have he : e.symm x = 0 := Algebra.norm_eq_zero_iff.mp ((mul_eq_zero.mp hx).resolve_left a.ne_zero)
    apply e.symm.injective
    simpa only [map_zero] using he
  obtain ⟨c, hc, hlow⟩ := ProperQuadratic.Construction.anisotropic_quadratic_lower_bound q hq hhom hzero
  let B := (a : F) • LinearMap.BilinForm.congr e.toLinearEquiv (NormPolarForm.Construction.normPolarForm σ)
  have hadd (v x : Local.FunctionsMetaplectic.Construction.Position F 2) : q (v + x) = q v + q x + BilinearFourierCoordinates.Construction.finiteBilinearContinuous B v x := by
    change (a : F) * Algebra.norm F (e.symm (v + x)) =
      (a : F) * Algebra.norm F (e.symm v) + (a : F) * Algebra.norm F (e.symm x) +
        (a : F) * NormPolarForm.Construction.normPolarForm σ (e.symm v) (e.symm x)
    rw [map_add, NormPolarForm.Construction.quadratic_norm_add σ hQuadratic hne]
    ring
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position F 2) := μ.map e
  have hνstable (r : ℝ) (hr : R ≤ r) :
      (∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x ∂ν) = Γ := by
    change (∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x ∂μ.map e.toHomeomorph) = _
    rw [e.toHomeomorph.isClosedEmbedding.integral_map, ← hstable r hr]
    unfold UltraNormGaussian.Construction.normGaussianCutoff
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) (e x) =
        (Metric.closedBall (0 : F) r).indicator (fun x => ψ x) ((a : F) * Algebra.norm F x)
      have hqe : q (e x) = (a : F) * Algebra.norm F x := by simp only [q, e.symm_apply_apply]
      by_cases hx : (a : F) * Algebra.norm F x ∈ Metric.closedBall (0 : F) r
      · have hex : e x ∈ q ⁻¹' Metric.closedBall 0 r := by
          change q (e x) ∈ Metric.closedBall (0 : F) r
          rwa [hqe]
        rw [Set.indicator_of_mem hex, Set.indicator_of_mem hx, hqe]
      · have hex : e x ∉ q ⁻¹' Metric.closedBall 0 r := by
          change q (e x) ∉ Metric.closedBall (0 : F) r
          rwa [hqe]
        rw [Set.indicator_of_notMem hex, Set.indicator_of_notMem hx]
  have hΓ := GaussianCutoff.Construction.anisotropic_hasGaussianCutoffs ν ψ q hq hp (BilinearFourierCoordinates.Construction.finiteBilinearContinuous B) hadd
    c hc hlow Γ R hνstable
  have ht := hΓ.transport e.toContinuousAddEquiv μ ψ q Γ
  change GaussianCutoff.Construction.HasGaussianCutoffs μ ψ (fun x => (a : F) * Algebra.norm F (e.symm (e x))) Γ at ht
  simpa only [e.symm_apply_apply] using ht

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianCutoffs.Construction
