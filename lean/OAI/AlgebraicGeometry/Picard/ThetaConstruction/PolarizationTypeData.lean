import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization

/-! # Polarization Type Data -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationTypeData.Geometric

noncomputable section

/-! The ordered polarization type is constructed from the fixed
integer matrix itself, independently of the period or its algebraization. -/

variable {g : ℕ}

structure IntegralPolarizationType (E : DefinitionsIntegral.IntegralMatrix g) where
  elementaryDivisors : Fin g → ℕ
  positive : ∀ i, 0 < elementaryDivisors i
  ordered : ∀ i j, i ≤ j → elementaryDivisors i ∣ elementaryDivisors j
  cokernel : (((DefinitionsIntegral.Index g → ℤ) →ₗ[ℤ] ℤ) ⧸ (Matrix.toBilin' E).range) ≃+
    ((∀ i : Fin g, ZMod (elementaryDivisors i)) × (∀ i : Fin g, ZMod (elementaryDivisors i)))

theorem integralPolarizationType_nonempty (E : DefinitionsIntegral.IntegralMatrix g)
    (hE : E.transpose = -E) (hEdet : E.det ≠ 0) : Nonempty (IntegralPolarizationType E) := by
  have halt : (Matrix.toBilin' E).IsAlt := by
    intro n
    have h := DefinitionsIntegral.Geometric.integerBilin_skew E hE n n
    omega
  have hnd : ∀ n : DefinitionsIntegral.Index g → ℤ, (∀ m, Matrix.toBilin' E n m = 0) → n = 0 :=
    (Matrix.nondegenerate_of_det_ne_zero hEdet).toBilin'.1
  obtain ⟨k, d, hk, hpos, hchain, ⟨e⟩⟩ :=
    HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.PolarizationType.polarization_type_exists halt hnd
  have hdim : 2 * g = 2 * k := by
    simpa only [DefinitionsIntegral.Index, Module.finrank_fin_fun] using hk
  have heq : k = g := by omega
  subst k
  exact ⟨⟨d, hpos, hchain, e⟩⟩

def integralPolarizationTypeData (E : DefinitionsIntegral.IntegralMatrix g)
    (hE : E.transpose = -E) (hEdet : E.det ≠ 0) : IntegralPolarizationType E :=
  Classical.choice (integralPolarizationType_nonempty E hE hEdet)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationTypeData.Geometric
