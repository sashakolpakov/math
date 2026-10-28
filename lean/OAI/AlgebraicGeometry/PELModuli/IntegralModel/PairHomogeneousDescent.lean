import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardFppfMap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardBaseChange

/-! # Pair Homogeneous Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairHomogeneousDescent

noncomputable section

/-! Homogeneity of a line on an abelian pair descends through an actual
surjective fppf base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem pairLine_homogeneous_of_baseChange {S T : Scheme.{u}} {g : ℕ}
    (A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : T ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.scheme ⊗ A.scheme).left)
    (h : (A.pullback b).IsHomogeneousPicardClass (D.pullback b).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme)))) :
    A.IsHomogeneousPicardClass D.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  let r := AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b
  have : Flat r.left := by
    change Flat (𝟙 _ ≫ pullback.fst D.scheme.hom b)
    infer_instance
  have : Surjective r.left := by
    change Surjective (𝟙 _ ≫ pullback.fst D.scheme.hom b)
    infer_instance
  have : LocallyOfFinitePresentation r.left := by
    change LocallyOfFinitePresentation (𝟙 _ ≫ pullback.fst D.scheme.hom b)
    infer_instance
  apply HomogeneousPicardFppfMap.homogeneousPicard_of_fppf_map A r (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  exact (congrArg (A.IsHomogeneousPicardClass ((Over.map b).obj (D.pullback b).scheme))
    (PairPicardBaseChange.pairLinePullback_class A D b L)).mp
      (A.isHomogeneousPicardClass_baseChange b (D.pullback b).scheme _ h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairHomogeneousDescent
