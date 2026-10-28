import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TateDegree

/-! # Tate Degree Resultant Norm -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TateDegreeResultantNorm

noncomputable section

/-! A finite étale polynomial in a genuine algebraic endomorphism has
equal resultant norms for its Tate and geometric degree polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  [Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)]
  [Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)]

include hℓ

theorem resultant_norm (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ)
    [IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left]
    [Surjective (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left]
    [Etale (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left] :
    ‖((Integral.TateNaturality.tateAction ℓ A F).baseChange ℚ_[ℓ]).charpoly.resultant
      (R.map (Nat.castRingHom ℚ_[ℓ]))‖ =
    ‖((Geometric.DegreeResultant.integerPolynomial A F).map (Int.castRingHom ℚ_[ℓ])).resultant
      (R.map (Nat.castRingHom ℚ_[ℓ]))‖ := by
  rw [← Intrinsic.TatePolynomialDeterminant.determinant_eval_nat, LinearMap.det_baseChange, Intrinsic.TatePolynomialDeterminant.tateAction_eq,
    Geometric.DegreeResultant.resultant_eq_residueDegree]
  exact FiniteEtale.TateDegree.determinant_norm A ℓ hℓ (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TateDegreeResultantNorm
