import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Pi

/-! # Basis Coordinate Split -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BasisCoordinateSplit.BundleCycles

noncomputable section

/-! A basis splits off one actual coordinate, with the chosen basis
vector identified with the distinguished augmentation variable. -/

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

def piCoordinateSplit (i : ι) : (ι → R) ≃ₗ[R] R × ({j : ι // j ≠ i} → R) := by
  classical
  exact {
    toFun := fun v => (v i, fun j => v j)
    invFun := fun v j => if h : j = i then v.1 else v.2 ⟨j, h⟩
    left_inv := fun v => by
      funext j
      change (if h : j = i then v i else v j) = v j
      split_ifs with h
      · exact h ▸ rfl
      · rfl
    right_inv := fun v => by apply Prod.ext; simp; funext j; simp [j.property]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def basisCoordinateSplit (b : Module.Basis ι R M) (i : ι) :
    M ≃ₗ[R] R × ({j : ι // j ≠ i} → R) := b.equivFun.trans (piCoordinateSplit i)

theorem basisCoordinateSplit_basis (b : Module.Basis ι R M) (i : ι) :
    basisCoordinateSplit b i (b i) = (1, 0) := by
  classical
  apply Prod.ext
  · change b.equivFun (b i) i = 1
    simp
  · funext j
    change b.equivFun (b i) j.val = 0
    simp [Ne.symm j.property]

theorem basisCoordinateSplit_symm_variable (b : Module.Basis ι R M) (i : ι) :
    (basisCoordinateSplit b i).symm (1, 0) = b i :=
  (basisCoordinateSplit b i).symm_apply_eq.mpr (basisCoordinateSplit_basis b i).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BasisCoordinateSplit.BundleCycles
