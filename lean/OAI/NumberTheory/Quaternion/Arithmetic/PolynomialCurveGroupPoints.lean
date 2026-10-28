import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialMatrixCurves
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm

/-! # Polynomial Curve Group Points -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PolynomialCurveGroupPoints

noncomputable section

/-! A polynomial matrix curve whose natural-number values belong to
an algebraic group belongs to that group at every field parameter. -/

open scoped Classical

variable {F K : Type} [Field F] [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
theorem evalPolynomialMatrix_det (P : Matrix (Fin n) (Fin n) (Polynomial K)) (t : K) :
    P.det.eval t = (PolynomialMatrixCurves.evalPolynomialMatrix P t).det :=
  RingHom.map_det (Polynomial.evalRingHom t) P

omit [CharZero K] in
theorem eval_polynomial_matrix_equation (ρ : F →+* K)
    (P : Matrix (Fin n) (Fin n) (Polynomial K)) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n F) (t : K) :
    (MvPolynomial.eval₂Hom (Polynomial.C.comp ρ) (fun ij => P ij.1 ij.2) p).eval t =
      MvPolynomial.eval₂Hom ρ (fun ij => PolynomialMatrixCurves.evalPolynomialMatrix P t ij.1 ij.2) p := by
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂Hom (Polynomial.C.comp ρ) _ p) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom t).comp (Polynomial.C.comp ρ) = ρ := by
    ext c
    exact Polynomial.eval_C
  rw [hc]
  rfl

theorem polynomial_curve_mem_group_of_nat (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ρ : F →+* K)
    (P : Matrix (Fin n) (Fin n) (Polynomial K))
    (hNat : ∀ m : ℕ, ∃ g : G.Points ρ, PolynomialGaloisNorm.matrixPointsHom G ρ g = PolynomialMatrixCurves.evalPolynomialMatrix P (m : K))
    (t : K) : ∃ g : G.Points ρ, PolynomialGaloisNorm.matrixPointsHom G ρ g = PolynomialMatrixCurves.evalPolynomialMatrix P t := by
  have hdetP : P.det = 1 := by
    apply BinomialPolynomials.polynomial_eq_of_nat_evaluations
    intro m
    obtain ⟨g, hg⟩ := hNat m
    rw [Polynomial.eval_one, evalPolynomialMatrix_det, ← hg]
    exact g.val.property
  have hdet : (PolynomialMatrixCurves.evalPolynomialMatrix P t).det = 1 := by
    rw [← evalPolynomialMatrix_det, hdetP, Polynomial.eval_one]
  let g : ArithmeticGroups.Lattices.Algebraic.SL n K := ⟨PolynomialMatrixCurves.evalPolynomialMatrix P t, hdet⟩
  have hmem : g ∈ G.subgroup K ρ := by
    apply (G.mem_iff K ρ g).mpr
    intro p hp
    have hzero : MvPolynomial.eval₂Hom (Polynomial.C.comp ρ) (fun ij => P ij.1 ij.2) p = 0 := by
      apply BinomialPolynomials.polynomial_eq_of_nat_evaluations
      intro m
      obtain ⟨g₀, hg₀⟩ := hNat m
      rw [Polynomial.eval_zero, eval_polynomial_matrix_equation, ← hg₀]
      exact (G.mem_iff K ρ g₀.val).mp g₀.property p hp
    change MvPolynomial.eval₂Hom ρ (fun ij => PolynomialMatrixCurves.evalPolynomialMatrix P t ij.1 ij.2) p = 0
    rw [← eval_polynomial_matrix_equation, hzero, Polynomial.eval_zero]
  exact ⟨⟨g, hmem⟩, rfl⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.PolynomialCurveGroupPoints
