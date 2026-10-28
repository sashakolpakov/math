import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraNormGaussian

/-! # Norm Gaussian Nonzero -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianNonzero.Construction

noncomputable section

/-! Nonvanishing of the stable nonarchimedean quadratic norm Gaussian. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

theorem exists_large_norm_gaussian_ne_zero
    {F E : Type} [NontriviallyNormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E]
    [FiniteDimensional F E] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (μE : Measure E) [μE.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) (R₀ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ R₀ ≤ r ∧ UltraNormGaussian.Construction.normGaussianCutoff μE ψ 1 r ≠ 0 := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let e := QuadraticNorm.Construction.quadraticFieldCoordinates hF hEmbedding hQuadratic
  let q : Local.FunctionsMetaplectic.Construction.Position F 2 → F := fun x => Algebra.norm F (e.symm x)
  have hq : Continuous q := (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding).comp e.symm.continuous
  have hp : IsProperMap q := (NormHaar.Construction.quadraticNorm_isProperMap hF hEmbedding hQuadratic).comp
    e.symm.toHomeomorph.isProperMap
  have hq0 : q 0 = 0 := by simp [q]
  have hqh (a : F) (x : Local.FunctionsMetaplectic.Construction.Position F 2) : q (a • x) = a ^ 2 * q x := by
    dsimp only [q]
    rw [map_smul, Algebra.smul_def, map_mul, Algebra.norm_algebraMap, hQuadratic]
  have hqz (x : Local.FunctionsMetaplectic.Construction.Position F 2) (hx : q x = 0) : x = 0 := by
    apply e.symm.injective
    simpa only [map_zero] using Algebra.norm_eq_zero_iff.mp hx
  obtain ⟨c, hcpos, hlow⟩ := ProperQuadratic.Construction.anisotropic_quadratic_lower_bound q hq hqh hqz
  let B := LinearMap.BilinForm.congr e.toLinearEquiv (NormPolarForm.Construction.normPolarForm σ)
  have hB : B.Nondegenerate := (NormPolarForm.Construction.normPolarForm_nondegenerate σ).congr e.toLinearEquiv
  have hBapp (v x : Local.FunctionsMetaplectic.Construction.Position F 2) : B v x = NormPolarForm.Construction.normPolarForm σ (e.symm v) (e.symm x) := rfl
  have hadd (v x : Local.FunctionsMetaplectic.Construction.Position F 2) : q (v + x) = q v + q x + BilinearFourierCoordinates.Construction.finiteBilinearContinuous B v x := by
    rw [BilinearFourierCoordinates.Construction.finiteBilinearContinuous_apply, hBapp]
    dsimp only [q]
    rw [map_add, NormPolarForm.Construction.quadratic_norm_add σ hQuadratic hne]
  obtain ⟨A, hA⟩ := BilinearFourierCoordinates.Construction.exists_gaussian_fourier_shift B hB
  obtain ⟨r, hr, hRr, hnonzero⟩ := QuadraticCutoffNe.Construction.exists_large_quadratic_cutoff_integral_ne_zero hF ψ hc hu hn
    q hq hp hq0 (BilinearFourierCoordinates.Construction.finiteBilinearContinuous B) hadd A hA c hcpos hlow R₀
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position F 2) := μE.map e
  let : ν.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μE
  let k := Measure.addHaarScalarFactor ν (Weak.Construction.referencePositionMeasure F 2)
  have hk : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (Weak.Construction.referencePositionMeasure F 2)
  have hν : ν = k • Weak.Construction.referencePositionMeasure F 2 :=
    Measure.isAddLeftInvariant_eq_smul_of_regular ν (Weak.Construction.referencePositionMeasure F 2)
  have heq : UltraNormGaussian.Construction.normGaussianCutoff μE ψ 1 r =
      ∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x ∂ν := by
    change _ = ∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x ∂μE.map e.toHomeomorph
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    unfold UltraNormGaussian.Construction.normGaussianCutoff
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (Metric.closedBall (0 : F) r).indicator (fun u => ψ u) (1 * Algebra.norm F x) =
        (q ⁻¹' Metric.closedBall 0 r).indicator (fun u => ψ (q u)) (e x)
      have hqe : q (e x) = Algebra.norm F x := by simp only [q, e.symm_apply_apply]
      rw [one_mul]
      by_cases hx : Algebra.norm F x ∈ Metric.closedBall 0 r
      · have hex : e x ∈ q ⁻¹' Metric.closedBall 0 r := by
          change q (e x) ∈ Metric.closedBall (0 : F) r
          rwa [hqe]
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hex, hqe]
      · have hex : e x ∉ q ⁻¹' Metric.closedBall 0 r := by
          change q (e x) ∉ Metric.closedBall (0 : F) r
          rwa [hqe]
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hex]
  refine ⟨r, hr, hRr, ?_⟩
  rw [heq, hν, integral_smul_nnreal_measure]
  exact smul_ne_zero hk.ne' hnonzero

theorem ultra_norm_gaussian_formula
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E]
    [FiniteDimensional F E] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) :
    ∃ Γ : ℂ, Γ ≠ 0 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ a : Fˣ,
      (FieldModulus.Construction.fieldModulus F a : ℂ) * UltraNormGaussian.Construction.normGaussianCutoff μE ψ (a : F) r = (ω a : ℂ) * Γ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · obtain ⟨R, hR, hstable⟩ := UltraNormGaussian.Construction.ultra_norm_gaussian_stable hF hE hEmbedding hQuadratic σ hne ω hω
      μF μE ψ hc hn
    obtain ⟨r, -, hr, hnonzero⟩ := exists_large_norm_gaussian_ne_zero hF hEmbedding hQuadratic σ hne
      μE ψ hc hu hn R
    have hh := hstable r hr 1
    simp only [map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Circle.coe_one, one_mul] at hh
    have hΓ : UltraNormGaussian.Construction.normGaussianCutoff μE ψ 1 R ≠ 0 := hh ▸ hnonzero
    exact ⟨UltraNormGaussian.Construction.normGaussianCutoff μE ψ 1 R, hΓ, R, hR, hstable⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianNonzero.Construction
