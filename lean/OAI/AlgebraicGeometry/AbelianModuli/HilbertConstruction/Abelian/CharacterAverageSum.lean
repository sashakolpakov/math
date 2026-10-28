import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterWeightedOperators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CharacterSums

/-! # Character Average Sum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.CharacterAverageSum

noncomputable section

/-! The character-average idempotents sum to one for every action of a tame finite abelian group in a coefficient algebra. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [Fintype (G →* Kˣ)]
    (B : Type w) [Ring B] [Algebra K B]

theorem characterAverageOperator_sum (ρ : G →* B) (hG : (Fintype.card G : K) ≠ 0) :
    ∑ χ : G →* Kˣ, CharacterWeightedOperators.characterAverageOperator K G B ρ χ = 1 := by
  classical
  calc
    ∑ χ : G →* Kˣ, CharacterWeightedOperators.characterAverageOperator K G B ρ χ =
        (Fintype.card G : K)⁻¹ • (∑ χ : G →* Kˣ, ∑ a : G, (χ a : K)⁻¹ • ρ a) :=
      Finset.smul_sum.symm
    _ = (Fintype.card G : K)⁻¹ • (∑ a : G, ∑ χ : G →* Kˣ, (χ a : K)⁻¹ • ρ a) :=
      congrArg (fun z : B => (Fintype.card G : K)⁻¹ • z) Finset.sum_comm
    _ = (Fintype.card G : K)⁻¹ • (∑ a : G, (∑ χ : G →* Kˣ, (χ a : K)⁻¹) • ρ a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_smul.symm
    _ = (Fintype.card G : K)⁻¹ • (∑ a : G, (if a = 1 then (Fintype.card G : K) else 0) • ρ a) := by
      simp only [Dual.CharacterSums.finiteCharacters_sum_inv_apply]
    _ = 1 := by simp [smul_smul, hG]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.CharacterAverageSum
