import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularization
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedTensorGaussian

/-! # Weighted Gaussian Regularization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedGaussianRegularization.Construction

noncomputable section

/-! Weighted multiplicities in regularized Hermitian Gaussian phases. -/

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

theorem weightedTensor_hasGaussianRegularization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hE : ¬ DiscreteTopology E) (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : Fˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => (t : F) * Algebra.norm F x) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (ω t : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ)
    {m n : ℕ} (μ : Measure (Fin (m * n) → E)) [μ.IsAddHaarMeasure] [μ.Regular]
    (Q : Matrix (Fin m) (Fin m) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin n → Fˣ) (χ : Eˣ →ₜ* Circle) (hχ : Characters.Construction.HasSplittingRestriction ω n χ)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    ∃ Z : ℂ, Z ≠ 0 ∧ QuadraticGaussianRegularization.Construction.HasGaussianRegularization μ ψ
      (HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ (TensorUnitary.Construction.weightedTensorForm Q a)
        (TensorUnitary.Construction.weightedTensorUnitary σ Q a g) (TensorUnitary.Construction.weightedTensorUnitary σ Q a h))) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = ((WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a m *
        GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g * GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ h *
          (GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ (g * h))⁻¹ : Circle) : ℂ) := by
  obtain ⟨b, hb⟩ := TensorUnitary.Construction.unitaryProductForm_det_in_base σ Q hQuadratic hne hQ hskew g h hg hh hgh
  let G := TensorUnitary.Construction.weightedTensorUnitary σ Q a
  have hGgh : G g * G h ∈ Generic.Construction.unitaryGenericDomain σ (TensorUnitary.Construction.weightedTensorForm Q a) := by
    rw [← map_mul]
    exact TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a (g * h) hgh
  obtain ⟨Z, hZ, hcut, hphase⟩ := GaussianRegularization.Construction.unitary_product_hasGaussianRegularization hE hQuadratic σ hne ω hω
    μE ψ Γ hΓ0 hΓ μ (TensorUnitary.Construction.weightedTensorForm Q a) (TensorUnitary.Construction.weightedTensorForm_nondegenerate Q hQ a)
    (TensorUnitary.Construction.weightedTensorForm_skew σ Q hskew a) (G g) (G h)
    (TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a g hg) (TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a h hh) hGgh
    (b ^ n * (∏ i, a i) ^ m) (TensorUnitary.Construction.weightedTensor_product_discriminant σ Q a g h hgh b hb)
  have hS : GenericDeterminantCharacter.Construction.unitCharacterValue χ (CayleyProduct.Construction.unitaryProductForm σ Q g h).det = ω b ^ n := by
    have hSn := CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh
    rw [GenericDeterminantCharacter.Construction.unitCharacterValue_apply χ _ hSn]
    have he : Units.mk0 (CayleyProduct.Construction.unitaryProductForm σ Q g h).det hSn =
        Units.map (algebraMap F E).toMonoidHom b := Units.ext hb.symm
    rw [he, hχ]
  have hcor : WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a m *
      GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g * GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ h *
      (GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ (g * h))⁻¹ =
        WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a m * ω b ^ n := by
    rw [← hS, GenericDeterminantCharacter.Construction.genericDeterminantCharacter_product σ Q hQ χ g h hg hh hgh]
    ac_rfl
  refine ⟨Z, hZ, hcut, ?_⟩
  rw [hphase, hcor, map_mul, map_pow, map_pow, Circle.coe_mul, Circle.coe_pow,
    Circle.coe_pow, Circle.coe_mul]
  change (GaussianFormula.Construction.normWeilConstant ω Γ hΓ0 : ℂ) ^ (m * n) *
      ((ω b : ℂ) ^ n * (ω (∏ i, a i) : ℂ) ^ m) =
    (((GaussianFormula.Construction.normWeilConstant ω Γ hΓ0 ^ (m * n) * ω (∏ i, a i) ^ m : Circle) : ℂ) * (ω b : ℂ) ^ n)
  rw [Circle.coe_mul, Circle.coe_pow, Circle.coe_pow]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedGaussianRegularization.Construction
