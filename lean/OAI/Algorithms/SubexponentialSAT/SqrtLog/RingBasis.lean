import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

namespace OAI.Algorithms

/-! Finite multiplication tables for any monic polynomial quotient. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingBasis

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A] {d : ℕ}
variable (F : A[X]) (hF : F.Monic) (hdegree : F.natDegree = d)

abbrev R := LiftRing.Extension F

def coordinates : R F ≃ₗ[A] (Fin d → A) :=
  SubexpActualRing.coordinatesOfDegree F hF hdegree

def basis (i : Fin d) : R F := LiftRing.mk F (X ^ (i : ℕ))

def structureConstant (i j k : Fin d) : A :=
  (X ^ ((i : ℕ) + (j : ℕ)) %ₘ F).coeff (k : ℕ)

@[simp] theorem coordinates_apply (x : R F) (i : Fin d) :
    coordinates F hF hdegree x i = (LiftRing.remainder hF x).coeff i :=
  SubexpActualRing.coordinatesOfDegree_apply _ _ _ x i

/-- Reconstruction from d coordinates uses the ordinary quotient power basis. -/
theorem reconstruct (x : R F) :
    (∑ i : Fin d, LiftRing.of F (coordinates F hF hdegree x i) * basis F i) = x := by
  have hx := (coordinates F hF hdegree).symm_apply_apply x
  rw [coordinates, SubexpActualRing.coordinatesOfDegree_symm_apply] at hx
  calc
    _ = LiftRing.mk F (∑ i : Fin d, monomial i (coordinates F hF hdegree x i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← C_mul_X_pow_eq_monomial]
      simp only [basis, LiftRing.of, RingHom.comp_apply, map_mul]
    _ = x := hx

/-- A coefficient vector is reconstructed as this same finite linear sum. -/
theorem coordinates_symm (c : Fin d → A) :
    (coordinates F hF hdegree).symm c =
      ∑ i : Fin d, LiftRing.of F (c i) * basis F i := by
  rw [coordinates, SubexpActualRing.coordinatesOfDegree_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial]
  simp only [basis, LiftRing.of, RingHom.comp_apply, map_mul]

theorem basis_mul_coordinates (i j k : Fin d) :
    coordinates F hF hdegree (basis F i * basis F j) k = structureConstant F i j k := by
  rw [coordinates_apply]
  simp only [basis, ← map_mul, ← pow_add, LiftRing.remainder_mk, structureConstant]

include hF hdegree in
/-- The d^3 multiplication entries suffice for arbitrary quotient arithmetic. -/
theorem basis_mul (i j : Fin d) :
    basis F i * basis F j =
      ∑ k : Fin d, LiftRing.of F (structureConstant F i j k) * basis F k := by
  calc
    _ = ∑ k : Fin d, LiftRing.of F (coordinates F hF hdegree (basis F i * basis F j) k) * basis F k :=
      (reconstruct F hF hdegree _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [basis_mul_coordinates]

/-- The constant one has the unit vector at index zero. -/
theorem one_coordinates (hd : 0 < d) (i : Fin d) :
    coordinates F hF hdegree 1 i = if i.val = 0 then 1 else 0 := by
  rw [coordinates_apply]
  have hpos : 0 < F.natDegree := by omega
  have hone : (1 : R F) = LiftRing.of F 1 := (map_one _).symm
  rw [hone, LiftRing.remainder_of hF hpos]
  simp only [Polynomial.C_1, Polynomial.coeff_one]

end SubexponentialSAT.SqrtLog.RingBasis

end
end OAI.Algorithms
