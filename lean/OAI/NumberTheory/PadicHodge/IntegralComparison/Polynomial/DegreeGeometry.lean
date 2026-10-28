import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeBaseChange

/-! # Degree Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry.Law

noncomputable section

/-! The multiplicative polynomial-algebra law computes native generic
residue degrees at actual natural-coefficient endomorphism evaluations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialCoordinates

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def naturalEnd (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ) : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A :=
  Polynomial.eval₂ (Nat.castRingHom (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)) F R

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem naturalEnd_eq_sum (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ)
    (n : ℕ) (hn : R.natDegree ≤ n) :
    naturalEnd A F R = ∑ i : Fin (n + 1), R.coeff i • F ^ (i : ℕ) := by
  unfold naturalEnd
  conv_lhs => rw [Finite.PolynomialCoordinates.expansion R n hn]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, nsmul_eq_mul]
  rfl

theorem norm_map_nat (L : Type*) [CommRing L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ)
    [IsFinite (naturalEnd A F R).toMul.hom.hom.left]
    [IsDominant (naturalEnd A F R).toMul.hom.hom.left] :
    DegreeBaseChange.Law.norm A L F (R.map (Nat.castRingHom L)) =
      ((naturalEnd A F R).toMul.hom.hom.left.residueDegree (genericPoint A.left) : L) := by
  rw [DegreeBaseChange.Law.norm_eq_valueBound A L F _ R.natDegree Polynomial.natDegree_map_le]
  have he := naturalEnd_eq_sum A F R R.natDegree le_rfl
  have : IsFinite (∑ i : Fin (R.natDegree + 1), R.coeff i • F ^ (i : ℕ)).toMul.hom.hom.left := by
    rw [← he]
    infer_instance
  have : IsDominant (∑ i : Fin (R.natDegree + 1), R.coeff i • F ^ (i : ℕ)).toMul.hom.hom.left := by
    rw [← he]
    infer_instance
  change DegreeNatural.LawScalarExtension.value A L _ _ = _
  simp only [Polynomial.coeff_map]
  change DegreeNatural.LawScalarExtension.value A L (fun i : Fin (R.natDegree + 1) => F ^ (i : ℕ))
    (fun i => (R.coeff i : L)) = _
  rw [DegreeNatural.LawScalarExtension.value_nat A L (fun i : Fin (R.natDegree + 1) => F ^ (i : ℕ))
    (fun i : Fin (R.natDegree + 1) => R.coeff i), ← he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry.Law
