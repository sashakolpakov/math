import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition

/-! # Split Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Chosen and opposite integral Tate blocks are the actual ranges of
the split completion's idempotents. Their sum is the original Tate module,
and the integral PEL action has the prescribed character on each block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)

def Data.SphericalPELAlbaneseData.integralTateBlock (v : Fin s × Bool) : Submodule ℤ_[q]
    (Add.schemeTateModule F.abelian.scheme T q) :=
  ProductActionDecomposition.ProductAction.block (D.splitTateAction h T F) v

instance Data.SphericalPELAlbaneseData.integralTateBlock_hasQuotient (v : Fin s × Bool) :
    HasQuotient (D.integralTateBlock h T F v)
      (Submodule ℤ_[q] (D.integralTateBlock h T F v)) :=
  Submodule.hasQuotient (R := ℤ_[q]) (M := D.integralTateBlock h T F v)

def Data.SphericalPELAlbaneseData.integralTateDecomposition :
    Add.schemeTateModule F.abelian.scheme T q ≃ₗ[ℤ_[q]] ∀ v, D.integralTateBlock h T F v :=
  ProductActionDecomposition.ProductAction.decomposition (D.splitTateAction h T F)

theorem Data.SphericalPELAlbaneseData.integralTateBlock_character (v : Fin s × Bool) (r : NumberField.RingOfIntegers E)
    (x : D.integralTateBlock h T F v) :
    Add.schemeTateMap F.abelian.scheme T q (End.endSchemeMap F.abelian.scheme (F.action r)) x.val =
      D.localCharacter v r • x.val := by
  rw [← D.splitTateAction_character h T F r]
  exact ProductActionDecomposition.ProductAction.action_on_block (D.splitTateAction h T F) _ v x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
