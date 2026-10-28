import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianRegularization
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula

/-! # Gaussian Regularization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularization.Construction

noncomputable section

/-! The regularized unitary-product Gaussian has the determinant phase. -/

open _root_.Matrix _root_.MeasureTheory

theorem unitary_product_hasGaussianRegularization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hE : ¬ DiscreteTopology E) (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ a : Fˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => (a : F) * Algebra.norm F x) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (ω a : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ)
    {d : ℕ} (μ : Measure (Fin d → E)) [μ.IsAddHaarMeasure] [μ.Regular]
    (Q : Matrix (Fin d) (Fin d) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (b : Fˣ) (hb : algebraMap F E (b : F) = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det) :
    ∃ Z : ℂ, Z ≠ 0 ∧ QuadraticGaussianRegularization.Construction.HasGaussianRegularization μ ψ
      (HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h)) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (GaussianFormula.Construction.normWeilConstant ω Γ hΓ0 : ℂ) ^ d * (ω b : ℂ) := by
  obtain ⟨a, ha, hchar⟩ := GaussianDiscriminant.Construction.unitaryProductGaussianMatrix_discriminant hQuadratic σ hne ω hω Q hQ g h b hb
  have hherm := GaussianDiscriminant.Construction.unitaryProductGaussianMatrix_hermitian σ Q hQ hskew g h hg hh hgh
    (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ)
  have hdet := GaussianDiscriminant.Construction.unitaryProductGaussianMatrix_nondegenerate σ Q hQ g h hg hh hgh
  obtain ⟨Z, hZ, hcut, hphase⟩ := HermitianGaussianRegularization.Construction.hermitian_hasGaussianRegularization hE hQuadratic σ hne ω hω
    μE ψ Γ hΓ μ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h) hherm hdet a ha
  refine ⟨Z, hZ, hcut, ?_⟩
  rw [hphase, hchar, Circle.coe_mul, Circle.coe_pow]
  change ((ω (Units.mk0 (1 / 2 : F) (one_div_ne_zero two_ne_zero)) : ℂ) ^ d * (ω b : ℂ)) *
    DiagonalNormGaussian.Construction.gaussianPhase Γ ^ d =
      (((ω (Units.mk0 (1 / 2 : F) (one_div_ne_zero two_ne_zero)) : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ) ^ d) * (ω b : ℂ)
  rw [mul_pow]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularization.Construction
