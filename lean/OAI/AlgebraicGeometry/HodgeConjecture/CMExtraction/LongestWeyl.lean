import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel

/-! # Longest Weyl -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LongestWeyl.Local

noncomputable section

/-! An actual integral determinant-one representative of the longest
Weyl element, including its signed reversal of matrix coordinates. -/

open scoped Classical _root_.Matrix

variable (R : Type*) [CommRing R]

def longestWeylMatrix : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem longestWeylMatrix_det : (longestWeylMatrix R).det = 1 := by
  simp [longestWeylMatrix, Matrix.det_fin_three]

def longestWeyl : Matrix.SpecialLinearGroup (Fin 3) R := ⟨longestWeylMatrix R, longestWeylMatrix_det R⟩

theorem longestWeyl_sq : longestWeyl R * longestWeyl R = 1 := by
  apply Subtype.ext
  change longestWeylMatrix R * longestWeylMatrix R = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longestWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem longestWeyl_inv : (longestWeyl R)⁻¹ = longestWeyl R :=
  (eq_inv_of_mul_eq_one_right (longestWeyl_sq R)).symm

def reversalSign (i : Fin 3) : R := if i = 1 then -1 else 1

theorem longestWeyl_conjugation_entry (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (longestWeylMatrix R * M * longestWeylMatrix R) i j =
      reversalSign R i * reversalSign R j * M i.rev j.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [longestWeylMatrix, reversalSign, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, Fin.ext_iff]

theorem longestWeyl_map {S : Type*} [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (longestWeyl R) = longestWeyl S := by
  apply Subtype.ext
  change (longestWeylMatrix R).map f = longestWeylMatrix S
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longestWeylMatrix]

theorem longestWeyl_integral (q : ℕ) [Fact q.Prime] :
    longestWeyl ℚ_[q] ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  ⟨longestWeyl ℤ_[q], longestWeyl_map ℤ_[q] PadicInt.Coe.ringHom⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LongestWeyl.Local
