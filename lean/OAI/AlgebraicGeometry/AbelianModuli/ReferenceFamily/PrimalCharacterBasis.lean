import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Primal Character Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimalCharacterBasis

noncomputable section

/-! A character basis of the actual dual space yields a character
basis of the original space, with the same character labels. -/

variable {k V I : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I k (Module.Dual k V))

def primalBasisOfDualBasis : Module.Basis I k V :=
  b.dualBasis.map (Module.evalEquiv k V).symm

theorem primalBasisOfDualBasis_pair (i j : I) :
    b j (primalBasisOfDualBasis b i) = if j = i then 1 else 0 := by
  rw [primalBasisOfDualBasis, Module.Basis.map_apply, Module.apply_evalEquiv_symm_apply,
    Module.Basis.dualBasis_apply_self]

theorem primalBasisOfDualBasis_eigen {R : Type*}
    (ρ : R → V →ₗ[k] V) (χ : I → R → k)
    (hb : ∀ i a, (ρ a).dualMap (b i) = χ i a • b i) (i : I) (a : R) :
    ρ a (primalBasisOfDualBasis b i) = χ i a • primalBasisOfDualBasis b i := by
  apply (Module.evalEquiv k V).injective
  apply b.ext
  intro j
  change b j (ρ a (primalBasisOfDualBasis b i)) = b j (χ i a • primalBasisOfDualBasis b i)
  have he := LinearMap.congr_fun (hb j a) (primalBasisOfDualBasis b i)
  change b j (ρ a (primalBasisOfDualBasis b i)) = χ j a * b j (primalBasisOfDualBasis b i) at he
  rw [he, map_smul, smul_eq_mul, primalBasisOfDualBasis_pair]
  split_ifs with h
  · subst j
    rfl
  · rw [mul_zero, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimalCharacterBasis
