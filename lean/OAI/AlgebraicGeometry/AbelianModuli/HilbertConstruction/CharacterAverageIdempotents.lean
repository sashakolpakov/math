import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterWeightedOperators

/-! # Character Average Idempotents -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAverageIdempotents

noncomputable section

/-! Tame character averages act as identity on their own eigenspace and vanish on different character eigenspaces; consequently they are orthogonal idempotents. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [Group G] [Fintype G]
    (B : Type w) [Ring B] [Algebra K B]

theorem characterAverageOperator_mul_eigen [DecidableEq (G →* Kˣ)]
    (ρ : G →* B) (χ ψ : G →* Kˣ) (v : B) (hG : (Fintype.card G : K) ≠ 0)
    (hv : ∀ a : G, ρ a * v = (ψ a : K) • v) :
    CharacterWeightedOperators.characterAverageOperator K G B ρ χ * v = if ψ = χ then v else 0 := by
  classical
  calc
    CharacterWeightedOperators.characterAverageOperator K G B ρ χ * v =
        (Fintype.card G : K)⁻¹ • (∑ a : G, (χ a : K)⁻¹ • (ρ a * v)) := by
      simp only [CharacterWeightedOperators.characterAverageOperator, CharacterWeightedOperators.characterWeightedOperator, smul_mul_assoc, Finset.sum_mul]
    _ = (Fintype.card G : K)⁻¹ • (∑ a : G, ((χ a : K)⁻¹ * (ψ a : K)) • v) := by
      simp only [hv, smul_smul]
    _ = (Fintype.card G : K)⁻¹ • ((∑ a : G, (χ a : K)⁻¹ * (ψ a : K)) • v) :=
      congrArg (fun z : B => (Fintype.card G : K)⁻¹ • z) Finset.sum_smul.symm
    _ = if ψ = χ then v else 0 := by
      rw [CharacterOrthogonality.finiteCharacter_orthogonality]
      split_ifs <;> simp [smul_smul, hG]

theorem characterAverageOperator_idempotent (ρ : G →* B) (χ : G →* Kˣ)
    (hG : (Fintype.card G : K) ≠ 0) :
    CharacterWeightedOperators.characterAverageOperator K G B ρ χ * CharacterWeightedOperators.characterAverageOperator K G B ρ χ =
      CharacterWeightedOperators.characterAverageOperator K G B ρ χ := by
  classical
  simpa using characterAverageOperator_mul_eigen K G B ρ χ χ
    (CharacterWeightedOperators.characterAverageOperator K G B ρ χ) hG (CharacterWeightedOperators.characterAverageOperator_left K G B ρ χ)

theorem characterAverageOperator_orthogonal (ρ : G →* B) (χ ψ : G →* Kˣ)
    (hG : (Fintype.card G : K) ≠ 0) (h : ψ ≠ χ) :
    CharacterWeightedOperators.characterAverageOperator K G B ρ χ * CharacterWeightedOperators.characterAverageOperator K G B ρ ψ = 0 := by
  classical
  simpa [h] using characterAverageOperator_mul_eigen K G B ρ χ ψ
    (CharacterWeightedOperators.characterAverageOperator K G B ρ ψ) hG (CharacterWeightedOperators.characterAverageOperator_left K G B ρ ψ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAverageIdempotents
