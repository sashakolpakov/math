import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant

/-! # Degree Polynomial Plus Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DegreePolynomialPlusNormalization.GeometricResultant

noncomputable section

/-! The reflected integer degree polynomial evaluates at -n as the
actual degree of [n]+F, whenever this map is finite and dominant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem integerPolynomial_eval_neg_nat (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ)
    [IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + F).toMul.hom.hom.left]
    [IsDominant ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + F).toMul.hom.hom.left] :
    (Geometric.DegreeResultant.integerPolynomial A F).eval (-(n : ℤ)) =
      (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + F).toMul.hom.hom.left.residueDegree
        (genericPoint A.left) : ℤ) := by
  let R : Polynomial ℕ := Polynomial.C n + Polynomial.X
  have he : IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R = (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + F := by
    simp only [IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd, R, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  let : IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left := he.symm ▸ inferInstance
  let : IsDominant (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left := he.symm ▸ inferInstance
  have hm : R.map (Nat.castRingHom ℚ) = Polynomial.C (n : ℚ) + Polynomial.X := by
    simp only [R, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]
    rfl
  have hv := IntegralComparison.Polynomial.DegreeBaseChange.Law.plusPolynomial_aeval A ℚ F (n : ℚ)
  rw [Polynomial.coe_aeval_eq_eval, ← hm, IntegralComparison.Polynomial.DegreeGeometry.Law.norm_map_nat, he] at hv
  apply Int.cast_injective (α := ℚ)
  have hw := congrArg (Polynomial.eval (-(n : ℚ))) (Geometric.DegreeResultant.integerPolynomial_map A F)
  rw [IntegralComparison.Polynomial.DegreeShift.Law.shiftPolynomial, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    neg_neg, hv] at hw
  have hcast : (-(n : ℚ)) = (Int.castRingHom ℚ) (-(n : ℤ)) := by simp
  rw [hcast, Polynomial.eval_map_apply] at hw
  exact hw

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DegreePolynomialPlusNormalization.GeometricResultant
