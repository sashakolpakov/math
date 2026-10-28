import OAI.NumberTheory.Quaternion.Arithmetic.SplitInverse
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

/-! # Split Polynomials -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomials

noncomputable section

/-! Polynomial coordinates for the split quaternion embedding of SL₂
in its four-dimensional regular matrix representation. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {F K : Type} [Field F] [Field K]

def quaternionSplitCoordinatePolynomials (a b x y : F) : Fin 4 → ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F :=
  let A : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F := MvPolynomial.X (0, 0)
  let B : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F := MvPolynomial.X (0, 1)
  let C : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F := MvPolynomial.X (1, 0)
  let D : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F := MvPolynomial.X (1, 1)
  ![(A + D) * MvPolynomial.C ((2 : F)⁻¹),
    (B + MvPolynomial.C a * C) * MvPolynomial.C ((2 * a)⁻¹),
    (MvPolynomial.C x * (A - D) - MvPolynomial.C y * (MvPolynomial.C a * C - B)) *
      MvPolynomial.C ((2 * b)⁻¹),
    (MvPolynomial.C x * (MvPolynomial.C a * C - B) - MvPolynomial.C a * MvPolynomial.C y * (A - D)) *
      MvPolynomial.C ((2 * a * b)⁻¹)]

def quaternionSplitRegularPolynomials (a b x y : F) : Matrix (Fin 4) (Fin 4) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 2 F) :=
  let q := quaternionSplitCoordinatePolynomials a b x y
  !![q 0, MvPolynomial.C a * q 1, MvPolynomial.C b * q 2, -MvPolynomial.C a * MvPolynomial.C b * q 3;
     q 1, q 0, MvPolynomial.C b * q 3, -MvPolynomial.C b * q 2;
     q 2, -MvPolynomial.C a * q 3, q 0, MvPolynomial.C a * q 1;
     q 3, -q 2, q 1, q 0]

theorem quaternionSplitCoordinatePolynomials_eval [CharZero K] (ρ : F →+* K)
    (a b x y : F) (M : Matrix (Fin 2) (Fin 2) K) :
    (fun i => MvPolynomial.eval₂Hom ρ (fun ij => M ij.1 ij.2)
      (quaternionSplitCoordinatePolynomials a b x y i)) =
      ![(SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) M).re,
        (SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) M).imI,
        (SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) M).imJ,
        (SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) M).imK] := by
  funext i
  fin_cases i <;> simp [quaternionSplitCoordinatePolynomials, SplitInverse.quaternionSplitInverse,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, map_ofNat]

theorem quaternionSplitRegularPolynomials_eval [CharZero K] (ρ : F →+* K)
    (a b x y : F) (M : Matrix (Fin 2) (Fin 2) K) :
    (quaternionSplitRegularPolynomials a b x y).map (MvPolynomial.eval₂Hom ρ (fun ij => M ij.1 ij.2)) =
      MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) (SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) M) := by
  have he := congrFun (quaternionSplitCoordinatePolynomials_eval ρ a b x y M)
  simp only [MvPolynomial.coe_eval₂Hom] at he
  rw [MatrixQuaternionDet.quaternionRegularMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionSplitRegularPolynomials, Matrix.cons_val_two, Matrix.cons_val_three, he]

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomials
