import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # Unitary Split Polynomials -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitarySplitPolynomials

noncomputable section

/-! Polynomial coordinates for the inverse SL(3) parametrization of
an arbitrary split Hermitian special-unitary group. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

def dualPolynomialMatrix (U V M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (U * M.adjugate * V).transpose

theorem dualPolynomialMatrix_map (U V M : Matrix (Fin 3) (Fin 3) R) (f : R →+* S) :
    (dualPolynomialMatrix U V M).map f = dualPolynomialMatrix (U.map f) (V.map f) (M.map f) := by
  change ((U * M.adjugate * V).map f).transpose = _
  apply congrArg Matrix.transpose
  change f.mapMatrix (U * M.adjugate * V) = _
  rw [map_mul, map_mul]
  change U.map f * M.adjugate.map f * V.map f = _
  exact congrArg (fun X : Matrix (Fin 3) (Fin 3) S => U.map f * X * V.map f) (f.map_adjugate M)

def quadraticPolynomialMatrix (d half invTwoRoot : R) (U V M : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) := fun i j =>
  ⟨(M i j + dualPolynomialMatrix U V M i j) * half,
    (M i j - dualPolynomialMatrix U V M i j) * invTwoRoot⟩

theorem quadraticPolynomialMatrix_map (d half invTwoRoot : R)
    (U V M : Matrix (Fin 3) (Fin 3) R) (f : R →+* S) :
    (quadraticPolynomialMatrix d half invTwoRoot U V M).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) =
      quadraticPolynomialMatrix (f d) (f half) (f invTwoRoot) (U.map f) (V.map f) (M.map f) := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) S => A i j) (dualPolynomialMatrix_map U V M f)
  change f (dualPolynomialMatrix U V M i j) = dualPolynomialMatrix (U.map f) (V.map f) (M.map f) i j at h
  apply QuadraticAlgebra.ext
  · change f ((M i j + dualPolynomialMatrix U V M i j) * half) = _
    simp only [quadraticPolynomialMatrix, map_mul, map_add, h, Matrix.map_apply]
  · change f ((M i j - dualPolynomialMatrix U V M i j) * invTwoRoot) = _
    simp only [quadraticPolynomialMatrix, map_mul, map_sub, h, Matrix.map_apply]

def regularPolynomialMatrix (d half invTwoRoot : R) (U V M : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 6) (Fin 6) R :=
  Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (quadraticPolynomialMatrix d half invTwoRoot U V M)

theorem regularPolynomialMatrix_map (d half invTwoRoot : R)
    (U V M : Matrix (Fin 3) (Fin 3) R) (f : R →+* S) :
    (regularPolynomialMatrix d half invTwoRoot U V M).map f =
      regularPolynomialMatrix (f d) (f half) (f invTwoRoot) (U.map f) (V.map f) (M.map f) := by
  rw [regularPolynomialMatrix, ← Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_map, quadraticPolynomialMatrix_map]
  rfl

end Ring

variable {F : Type} [Field F] [CharZero F] {d : F}
variable (r : F) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) (hH : H.val.conjTranspose = H.val)

theorem specialUnitaryEquivSL_inverse_matrix (A : Matrix.SpecialLinearGroup (Fin 3) F) :
    ((SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm A).val.val =
      quadraticPolynomialMatrix d (2⁻¹) ((2 * r)⁻¹)
        (SplitUnitary.plusUnits r hr hr0 H).val (SplitUnitary.plusUnits r hr hr0 H).inv A.val := by
  let e := SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH
  have hp : SplitUnitary.plusUnitary r hr hr0 H (SpecialUnitary.includeUnitary H.val (e.symm A)) =
      Matrix.SpecialLinearGroup.toGL A :=
    Units.ext (congrArg Subtype.val (e.apply_symm_apply A))
  have hl := SplitUnitary.liftLinear_recovers r hr hr0 H hH (SpecialUnitary.includeUnitary H.val (e.symm A))
  rw [hp] at hl
  change (e.symm A).val.val = _
  apply Eq.trans (congrArg Units.val hl).symm
  change SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A.val
    (dualPolynomialMatrix (SplitUnitary.plusUnits r hr hr0 H).val (SplitUnitary.plusUnits r hr hr0 H).inv A.val) = _
  apply Matrix.ext
  intro i j
  apply QuadraticAlgebra.ext
  · exact div_eq_mul_inv _ _
  · exact div_eq_mul_inv _ _

end

end OAI.RepresentationTheory.Theta.Adelic.UnitarySplitPolynomials
