import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Finite Module Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteModuleFieldDetection

noncomputable section

/-! A module finite over an algebra vanishes if all field-valued base changes of the ground ring vanish. -/

open scoped TensorProduct

universe u

theorem finiteAlgebraModule_subsingleton_of_fieldTensors
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Subsingleton (K ⊗[R] M)) : Subsingleton M := by
  apply HilbertScheme.Presentations.ResidueFieldDetection.finiteModule_subsingleton_of_residueFields S M
  intro p
  let K := p.asIdeal.ResidueField
  have : IsScalarTower R S K := inferInstance
  have : Subsingleton (K ⊗[R] M) := h K
  exact (TensorProduct.mapOfCompatibleSMul_surjective S R R K M).subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteModuleFieldDetection
