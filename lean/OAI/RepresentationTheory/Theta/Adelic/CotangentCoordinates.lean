import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Cotangent Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.CotangentCoordinates

noncomputable section

/-! Position coordinates together with their dual momentum coordinates
preserve the canonical pairing, over any field. -/

open scoped Classical

open _root_.Module _root_.Matrix
variable {R I J : Type*} [Field R] [Fintype I] [Fintype J]

theorem standard_dual_apply (x y : I → R) :
    (Pi.basisFun R I).toDual x y = ∑ i, x i * y i := by
  conv_lhs => rw [← (Pi.basisFun R I).sum_repr y]
  simp only [map_sum, map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr,
    smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

variable (e : (I → R) ≃ₗ[R] (J → R))

def coordinateBasis : Basis J R (I → R) := (Pi.basisFun R J).map e.symm

omit [Fintype I] in
theorem coordinateBasis_repr (x : I → R) (j : J) :
    (coordinateBasis e).repr x j = e x j := rfl

def cotangentCoordinates : (I → R) ≃ₗ[R] (J → R) :=
  (Pi.basisFun R I).toDualEquiv.trans (coordinateBasis e).dualBasis.equivFun

theorem cotangentCoordinates_apply (x : I → R) (j : J) :
    cotangentCoordinates e x j = ∑ i, x i * coordinateBasis e j i := by
  change (coordinateBasis e).dualBasis.repr ((Pi.basisFun R I).toDual x) j = _
  rw [Module.Basis.dualBasis_repr, standard_dual_apply]

theorem coordinate_pairing (x y : I → R) :
    ∑ j, e x j * cotangentCoordinates e y j = ∑ i, x i * y i := by
  have h := congrArg ((Pi.basisFun R I).toDual y) ((coordinateBasis e).sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul, coordinateBasis_repr] at h
  rw [standard_dual_apply] at h
  calc
    _ = ∑ j, e x j * (Pi.basisFun R I).toDual y (coordinateBasis e j) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact (cotangentCoordinates_apply e y j).trans (standard_dual_apply _ _).symm
    _ = ∑ i, y i * x i := h
    _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end

end OAI.RepresentationTheory.Theta.Adelic.CotangentCoordinates
