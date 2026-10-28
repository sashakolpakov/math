import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Position Basis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis.LocalAnalysis

noncomputable section

/-! Explicit finite position coordinates for a basis, with one index
for the position and one for the scalar-space basis. -/

open scoped Classical

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E] [Fintype ι]

def positionBasisCoordinates (N : ℕ) (b : Module.Basis ι R E) :
    (Fin N → E) ≃ₗ[R] ((Fin N × ι) → R) where
  toFun x p := b.equivFun (x p.1) p.2
  invFun y i := b.equivFun.symm (fun j => y (i, j))
  left_inv x := funext (fun i => b.equivFun.symm_apply_apply (x i))
  right_inv y := funext (fun p => congrFun (b.equivFun.apply_symm_apply (fun j => y (p.1, j))) p.2)
  map_add' x y := funext (fun p => congrFun (b.equivFun.map_add (x p.1) (y p.1)) p.2)
  map_smul' c x := funext (fun p => congrFun (b.equivFun.map_smul c (x p.1)) p.2)

def positionBasis (N : ℕ) (b : Module.Basis ι R E) : Module.Basis (Fin N × ι) R (Fin N → E) :=
  Module.Basis.ofEquivFun (positionBasisCoordinates N b)

theorem positionBasis_equivFun (N : ℕ) (b : Module.Basis ι R E) :
    (positionBasis N b).equivFun = positionBasisCoordinates N b :=
  Module.Basis.equivFun_ofEquivFun _

theorem positionBasis_equivFun_symm (N : ℕ) (b : Module.Basis ι R E) (y : (Fin N × ι) → R)
    (i : Fin N) : (positionBasis N b).equivFun.symm y i = b.equivFun.symm (fun j => y (i, j)) := by
  rw [positionBasis_equivFun]
  rfl

theorem positionBasis_apply (N : ℕ) (b : Module.Basis ι R E) (p : Fin N × ι) :
    positionBasis N b p = Pi.single p.1 (b p.2) := by
  apply (positionBasisCoordinates N b).injective
  have hp := (positionBasis N b).equivFun_self p
  rw [positionBasis_equivFun] at hp
  funext z
  rw [hp]
  by_cases h : z.1 = p.1
  · rcases z with ⟨i, j⟩
    dsimp only at h
    subst i
    rcases p with ⟨k, l⟩
    simp [positionBasisCoordinates, Finsupp.single_apply]
  · have hpz : p ≠ z := fun hz => h (congrArg Prod.fst hz).symm
    simp [positionBasisCoordinates, h, hpz]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis.LocalAnalysis
