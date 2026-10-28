import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicTatePolynomialAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree

/-! # Tate Polynomial Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant

noncomputable section

/-! Polynomial determinants in the native geometric-points presentation
of the Tate module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  (ℓ : ℕ) [Fact ℓ.Prime]
  [Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)]

omit [IsAlgClosed k] in
theorem determinant_eval_nat (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ) :
    ((Integral.TateNaturality.tateAction ℓ A (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R)).baseChange ℚ_[ℓ]).det =
      ((Integral.TateNaturality.tateAction ℓ A F).baseChange ℚ_[ℓ]).charpoly.resultant
        (R.map (Nat.castRingHom ℚ_[ℓ])) := by
  have h := AlgebraicTatePolynomialAction.determinant_eval₂_nat A (𝟙_ _) ℓ F R
  rw [AlgebraicTatePolynomialAction.rationalEndHom_apply,
    AlgebraicTatePolynomialAction.rationalEndHom_apply] at h
  exact h

omit [IsAlgClosed k] [Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)] in
theorem tateAction_eq (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    Integral.TateNaturality.tateAction ℓ A F = AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map ℓ (FiniteEtale.KernelDegree.pointAction A F.toMul.hom.hom) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant
