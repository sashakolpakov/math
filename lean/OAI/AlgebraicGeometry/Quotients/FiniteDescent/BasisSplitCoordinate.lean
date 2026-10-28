import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Prod

/-! # Basis Split Coordinate -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BasisSplitCoordinate.Construction.LocalSectionLifting

noncomputable section

/-! Splitting off one chosen basis coordinate for Gaussian cancellation. -/

variable {R ι : Type*} [CommRing R]

def piSplitCoordinate (i : ι) : (ι → R) ≃ₗ[R] (({j : ι // j ≠ i} → R) × R) := by
  classical
  exact
    { toFun := fun x => (fun j => x j, x i)
      invFun := fun x j => if h : j = i then x.2 else x.1 ⟨j, h⟩
      left_inv := by
        intro x
        funext j
        dsimp only
        split_ifs with h
        · exact congrArg x h.symm
        · rfl
      right_inv := by
        intro x
        apply Prod.ext
        · funext j
          simp [j.property]
        · simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

variable {M : Type*} [AddCommGroup M] [Module R M] [Fintype ι]

def basisSplitCoordinate (b : Module.Basis ι R M) (i : ι) :
    M ≃ₗ[R] (({j : ι // j ≠ i} → R) × R) :=
  b.equivFun.trans (piSplitCoordinate i)

theorem basisSplitCoordinate_scalar (b : Module.Basis ι R M) (i : ι) (x : M) :
    (basisSplitCoordinate b i x).2 = b.repr x i := rfl

theorem basisSplitCoordinate_basis (b : Module.Basis ι R M) (i : ι) :
    basisSplitCoordinate b i (b i) = (0, 1) := by
  classical
  apply Prod.ext
  · funext j
    change b.repr (b i) j = 0
    simp [Module.Basis.repr_self, j.property]
  · change b.repr (b i) i = 1
    simp

theorem basisSplitCoordinate_symm_scalar (b : Module.Basis ι R M) (i : ι) (r : R) :
    (basisSplitCoordinate b i).symm (0, r) = r • b i := by
  apply (basisSplitCoordinate b i).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, basisSplitCoordinate_basis]
  simp

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BasisSplitCoordinate.Construction.LocalSectionLifting
