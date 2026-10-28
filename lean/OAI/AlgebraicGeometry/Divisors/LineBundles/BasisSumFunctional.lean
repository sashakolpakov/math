import Mathlib.LinearAlgebra.Basis.Basic

/-! # Basis Sum Functional -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BasisSumFunctional.BundleCycles

noncomputable section

/-! The actual linear functional taking every basis vector to one. -/

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M)

def basisSumFunctional : M →ₗ[R] R := b.constr R (fun _ => 1)

theorem basisSumFunctional_basis (i : ι) : basisSumFunctional b (b i) = 1 :=
  b.constr_basis R (fun _ => 1) i

theorem basisSumFunctional_surjective [Nonempty ι] : Function.Surjective (basisSumFunctional b) := by
  intro r
  let i : ι := Classical.choice inferInstance
  refine ⟨r • b i, ?_⟩
  rw [map_smul, basisSumFunctional_basis, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BasisSumFunctional.BundleCycles
