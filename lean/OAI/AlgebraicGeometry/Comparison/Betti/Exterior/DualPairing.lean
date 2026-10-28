import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Dual Pairing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.DualPairing.LinearAlgebra

noncomputable section

/-! The canonical pairing between exterior powers and their duals is perfect in finite dimension. -/

variable {K E ι : Type} [Field K] [AddCommGroup E] [Module K E]
  [Finite ι] [LinearOrder ι]

def exteriorDualPairingEquiv (b : Module.Basis ι K E) (n : ℕ) :
    (⋀[K]^n (Module.Dual K E)) ≃ₗ[K] Module.Dual K (⋀[K]^n E) :=
  (b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)

theorem exteriorDualPairingEquiv_toLinearMap (b : Module.Basis ι K E) (n : ℕ) :
    (exteriorDualPairingEquiv b n).toLinearMap = exteriorPower.pairingDual K E n := by
  apply (b.dualBasis.exteriorPower n).ext
  intro s
  change (b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)
    ((b.dualBasis.exteriorPower n) s) = _
  rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  apply LinearMap.ext
  intro v
  rw [Module.Basis.dualBasis_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, Module.Basis.coe_dualBasis]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.DualPairing.LinearAlgebra
