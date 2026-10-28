import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Equivariance

/-! # Block Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual PEL isogenies induce maps on the chosen and opposite integral
Tate blocks, with no independent linear maps supplied as data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S}
  {n : ℕ} (e : PELIsogenies.PELIsogeny P Q n)

theorem Data.SphericalPELAlbaneseData.splitTateAction_commute (a : Fin s × Bool → ℤ_[q]) :
    (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom).comp (D.splitTateAction h T P a) =
      (D.splitTateAction h T Q a).comp (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom) :=
  e.tateCompletedAction_commute T q ((D.localCompletionEquivZq h).symm a)

def Data.SphericalPELAlbaneseData.tateBlockMap (v : Fin s × Bool) :
    D.integralTateBlock h T P v →ₗ[ℤ_[q]] D.integralTateBlock h T Q v :=
  ProductActionDecomposition.ProductAction.blockMap (D.splitTateAction h T P) (D.splitTateAction h T Q)
    (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom) (D.splitTateAction_commute h T e) v

theorem Data.SphericalPELAlbaneseData.tateBlockMap_val (v : Fin s × Bool) (x : D.integralTateBlock h T P v) :
    (D.tateBlockMap h T e v x).val = Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom x.val := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
