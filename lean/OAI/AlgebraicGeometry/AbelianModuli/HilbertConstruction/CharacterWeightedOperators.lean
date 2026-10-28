import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterOrthogonality

/-! # Character Weighted Operators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterWeightedOperators

noncomputable section

/-! Weighted finite averages in an arbitrary coefficient algebra transform according to their chosen character. This applies in particular to endomorphism algebras. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [Group G] [Fintype G]
    (B : Type w) [Ring B] [Algebra K B]

def characterWeightedOperator (ρ : G →* B) (χ : G →* Kˣ) : B :=
  ∑ a : G, (χ a : K)⁻¹ • ρ a

def characterAverageOperator (ρ : G →* B) (χ : G →* Kˣ) : B :=
  (Fintype.card G : K)⁻¹ • characterWeightedOperator K G B ρ χ

theorem characterWeightedOperator_left (ρ : G →* B) (χ : G →* Kˣ) (a : G) :
    ρ a * characterWeightedOperator K G B ρ χ = (χ a : K) • characterWeightedOperator K G B ρ χ := by
  calc
    ρ a * characterWeightedOperator K G B ρ χ =
        ∑ b : G, (χ b : K)⁻¹ • ρ (a * b) := by
      rw [characterWeightedOperator, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact (mul_smul_comm _ _ _).trans (congrArg (fun z : B => (χ b : K)⁻¹ • z) (ρ.map_mul a b).symm)
    _ = ∑ b : G, (χ a : K) • ((χ (a * b) : K)⁻¹ • ρ (a * b)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_smul]
      have h : (χ b : K)⁻¹ = (χ a : K) * (χ (a * b) : K)⁻¹ := by
        simp [mul_comm]
      exact congrArg (fun z : K => z • ρ (a * b)) h
    _ = ∑ b : G, (χ a : K) • ((χ b : K)⁻¹ • ρ b) :=
      Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
    _ = (χ a : K) • characterWeightedOperator K G B ρ χ := Finset.smul_sum.symm

theorem characterAverageOperator_left (ρ : G →* B) (χ : G →* Kˣ) (a : G) :
    ρ a * characterAverageOperator K G B ρ χ = (χ a : K) • characterAverageOperator K G B ρ χ := by
  rw [characterAverageOperator, mul_smul_comm, characterWeightedOperator_left, smul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterWeightedOperators
