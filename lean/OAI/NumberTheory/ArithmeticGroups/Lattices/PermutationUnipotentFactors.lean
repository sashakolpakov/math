import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousMaskedUnipotentFactors
import OAI.NumberTheory.ArithmeticGroups.Lattices.TransitiveMatrixSupport

/-! # Permutation Unipotent Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationUnipotentFactors.Construction

noncomputable section

/-! Continuous unipotent factors supported on the inverted and
preserved positive pairs of a permutation. -/

open NormedSpace

theorem weightRaising_support_upper
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (hw : Antitone w)
    (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (i j : Fin m) (hij : ¬i < j) : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X i j = 0 := by
  rw [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply]
  exact hX i j (hw (le_of_not_gt hij))

theorem weightRaising_permutation_unipotent_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (hw : Antitone w) (heig : ∀ i, H (b i) = w i • b i)
    (σ : Equiv.Perm (Fin m)) :
    ∃ u v : UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w → (L →L[ℝ] L)ˣ, Continuous u ∧ Continuous v ∧
      ∀ g, u g ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w ∧ v g ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w ∧
        (u g).val - 1 ∈ TransitiveMatrixSupport.Construction.operatorSupportSubmodule b (fun i j => i < j ∧ σ j < σ i) ∧
        (v g).val - 1 ∈ TransitiveMatrixSupport.Construction.operatorSupportSubmodule b (fun i j => i < j ∧ σ i < σ j) ∧
        g.val = u g * v g := by
  obtain ⟨X, Y, hX, hY, hf⟩ := ContinuousMaskedUnipotentFactors.Construction.weightRaising_continuous_masked_factors b H hH w heig
    (fun i j => σ j < σ i)
  refine ⟨fun g => OperatorExponentialUnits.Construction.operatorExpUnit (X g), fun g => OperatorExponentialUnits.Construction.operatorExpUnit (Y g),
    OperatorExponentialUnits.Construction.operatorExpUnit_continuous.comp hX, OperatorExponentialUnits.Construction.operatorExpUnit_continuous.comp hY, fun g => ?_⟩
  obtain ⟨hXW, hYW, hXS, hYS, he⟩ := hf g
  have hXI : X g ∈ TransitiveMatrixSupport.Construction.operatorSupportSubmodule b (fun i j => i < j ∧ σ j < σ i) := by
    intro i j hij
    by_cases hlt : i < j
    · rw [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply]
      exact hXS i j (fun h => hij ⟨hlt, h⟩)
    · exact weightRaising_support_upper b w hw _ hXW i j hlt
  have hYP : Y g ∈ TransitiveMatrixSupport.Construction.operatorSupportSubmodule b (fun i j => i < j ∧ σ i < σ j) := by
    intro i j hij
    by_cases hlt : i < j
    · rw [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply]
      apply hYS i j
      have hle : σ j ≤ σ i := le_of_not_gt (fun h => hij ⟨hlt, h⟩)
      exact lt_of_le_of_ne hle (fun heq => (ne_of_gt hlt) (σ.injective heq))
    · exact weightRaising_support_upper b w hw _ hYW i j hlt
  refine ⟨Weight.RaisingExponential.Construction.weightRaising_exp_sub_one_mem b w _ hXW, Weight.RaisingExponential.Construction.weightRaising_exp_sub_one_mem b w _ hYW,
    ?_, ?_, he⟩
  · exact TransitiveMatrixSupport.Construction.operatorSupportSubmodule_exp_sub_one b _
      (fun ⦃_ _ _⦄ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩) _ hXI
  · exact TransitiveMatrixSupport.Construction.operatorSupportSubmodule_exp_sub_one b _
      (fun ⦃_ _ _⦄ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩) _ hYP

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationUnipotentFactors.Construction
