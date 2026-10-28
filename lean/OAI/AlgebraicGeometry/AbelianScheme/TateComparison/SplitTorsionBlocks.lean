import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitActionEigenvectors
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision

/-! # Split Torsion Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitTorsionBlocks.SphericalPELAlbaneseData

noncomputable section

/-! Tate evaluation maps onto the actual split torsion blocks. Both
blocks are constructed from the same completed integral PEL action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)

local instance : Module ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  Add.Tate.torsion_padicModule q (Additive (T ⟶ F.abelian.scheme)) n

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.splitTorsionAction : (Fin s × Bool → ℤ_[q]) →ₐ[ℤ_[q]]
    Module.End ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  (TorsionAction.torsionCompletedAction T q n F).comp (D.localCompletionEquivZq h).symm.toAlgHom

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.torsionBlock (v : Fin s × Bool) :
    Submodule ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  ProductActionDecomposition.ProductAction.block (D.splitTorsionAction h T F n) v

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.splitTorsionAction_character (r : NumberField.RingOfIntegers E) :
    D.splitTorsionAction h T F n (fun v => D.localCharacter v r) = TorsionAction.torsionIntegralAction T q n F r := by
  have he : D.localCompletionEquivZq h (1 ⊗ₜ[ℤ] r) = fun v => D.localCharacter v r := by
    change (1 : ℤ_[q]) • (fun v => D.localCharacter v r) = _
    exact one_smul _ _
  rw [← he]
  change TorsionAction.torsionCompletedAction T q n F
    ((D.localCompletionEquivZq h).symm (D.localCompletionEquivZq h (1 ⊗ₜ[ℤ] r))) = _
  rw [AlgEquiv.symm_apply_apply, TorsionAction.torsionCompletedAction_tmul, one_smul]

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.evaluate_splitAction (a : Fin s × Bool → ℤ_[q]) :
    (Evaluation.Tate.evaluate q n).comp (D.splitTateAction h T F a) =
      (D.splitTorsionAction h T F n a).comp (Evaluation.Tate.evaluate q n) :=
  TorsionAction.evaluate_completedAction T q n F ((D.localCompletionEquivZq h).symm a)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.evaluateBlock (v : Fin s × Bool) :
    D.integralTateBlock h T F v →ₗ[ℤ_[q]] D.torsionBlock h T F n v :=
  ProductActionDecomposition.ProductAction.blockMap (D.splitTateAction h T F) (D.splitTorsionAction h T F n)
    (Evaluation.Tate.evaluate q n) (D.evaluate_splitAction h T F n) v

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometric_evaluateBlock_surjective {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k)))
    (v : Fin s × Bool) :
    Function.Surjective (D.evaluateBlock h (Over.mk (𝟙 (Spec (.of k)))) F n v) :=
  ProductActionDecomposition.ProductAction.blockMap_surjective _ _ _ _ (GeometricDivision.geometricTate_evaluate_surjective F.abelian q n) v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitTorsionBlocks.SphericalPELAlbaneseData
