import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Module.Projective

/-! # Projective Exterior -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveExterior.ProjectiveExteriorPower

noncomputable section

/-! Exterior powers of projective modules are projective over any commutative ring. -/

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]

theorem projective (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  apply Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id))
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveExterior.ProjectiveExteriorPower
