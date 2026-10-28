import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CharacterBasis

/-! # Character Orthogonality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterOrthogonality

noncomputable section

/-! Finite character sums give the algebraic orthogonality identities used in averaging projections. -/
universe u v
variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G]

theorem finiteCharacter_sum_eq_zero (χ : G →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : G, (χ a : K) = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : G, χ a ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext h)
  have haK : (χ a : K) ≠ 1 := fun h => ha (Units.ext h)
  let s : K := ∑ b : G, (χ b : K)
  have hshift : (χ a : K) * s = s := by
    change (χ a : K) * (∑ b : G, (χ b : K)) = _
    rw [Finset.mul_sum]
    calc
      ∑ b : G, (χ a : K) * (χ b : K) = ∑ b : G, (χ (a * b) : K) := by
        apply Finset.sum_congr rfl
        intro b _
        exact (congrArg (fun z : Kˣ => (z : K)) (χ.map_mul a b)).symm
      _ = s := Fintype.sum_equiv (Equiv.mulLeft a) (fun b : G => (χ (a * b) : K))
        (fun b : G => (χ b : K)) (fun _ => rfl)
  have hzero : ((χ a : K) - 1) * s = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr haK)

theorem finiteCharacter_orthogonality [DecidableEq (G →* Kˣ)] (χ ψ : G →* Kˣ) :
    ∑ a : G, (χ a : K)⁻¹ * (ψ a : K) = if ψ = χ then (Fintype.card G : K) else 0 := by
  classical
  by_cases h : ψ = χ
  · subst ψ
    simp
  · rw [ite_eq_right h]
    have hη : χ⁻¹ * ψ ≠ 1 := by
      intro he
      exact h (inv_mul_eq_one.mp he).symm
    simpa using finiteCharacter_sum_eq_zero (χ⁻¹ * ψ) hη

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterOrthogonality
