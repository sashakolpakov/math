import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LineHomDescent

/-! # Normalized Picard Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardDescent.RelativeNormalizedPicard

noncomputable section

/-! Effective descent of normalized line-bundle comparisons on an
abelian family over a reduced noetherian parameter. The comparison and
its Cech compatibility are constructed; no descent datum is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem normalize_descends {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {T U : Over S} [IsReduced T.left] [IsNoetherian T.left] (u : U ⟶ T)
    [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (L M : (T ⊗ A.scheme).left.Modules)
    (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M)
    (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    ∃! d : L ≅ M, (Scheme.Modules.pullback (u ▷ A.scheme).left).mapIso d =
      NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e :=
  Picard.LineHomDescent.PicardLineHomDescent.existsUnique_lineIso_descent (u ▷ A.scheme).left hL hM
    (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e) (NormalizedPicardOverlap.RelativeNormalizedPicard.normalize_compatible A u L M eL eM e hL)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardDescent.RelativeNormalizedPicard
