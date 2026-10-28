import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaPowers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaIsomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PowerLineIso

/-! # Positive Poincare Multiple -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositivePoincareMultiple

noncomputable section

/-! Construct the normalized ample inducing-line formula for every positive Poincare multiple. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type u} [Field k] {A D : Over (Spec (.of k))} [GrpObj A] [GrpObj D]
  (P : Line.Bundles.LineBundle (D ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P) (ell : A ⟶ D)

include Dh

/-- Positive tensor powers construct the ample line, origin frame, and full multiplication formula. -/
theorem positive_multiple
    (h : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A ((Line.Comparison.Bundle.toShared P).pullback (ell ⊗ₘ 𝟙 A).left))
    (n : ℕ) (hn : 0 < n) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A ((Line.Comparison.Bundle.toShared P).pullback ((ell ^ n) ⊗ₘ 𝟙 A).left) := by
  have hp := PositiveFormulaPowers.positive_power A ((Line.Comparison.Bundle.toShared P).pullback (ell ⊗ₘ 𝟙 A).left) h n hn
  obtain ⟨e⟩ := Poincare.PowerLineIso.exists_iso P Dh ell n
  exact PositiveFormulaIsomorphism.of_iso A _ _ e.symm hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositivePoincareMultiple
