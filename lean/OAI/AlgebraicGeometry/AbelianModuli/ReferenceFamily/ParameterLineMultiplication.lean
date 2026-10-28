import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PullbackTensorFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Parameter Line Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterLineMultiplication

noncomputable section

/-! Multiplication of the normalized Picard family is realized by
actual tensor isomorphisms of its line bundles on each qcqs test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eA : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule P.left)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [CompactSpace T.left] [QuasiSeparatedSpace T.left]

include eA in
theorem parameterLineClass_mul_of_picard (x y : T ⟶ P)
    (h : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q y := by
  let L := Q.pullback (x ⊗ₘ 𝟙 A.scheme).left
  let K := Q.pullback (y ⊗ₘ 𝟙 A.scheme).left
  let H := Q.pullback ((x * y) ⊗ₘ 𝟙 A.scheme).left
  let z := (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
  have hL : Nonempty ((Scheme.Modules.pullback z).obj L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left) :=
    Quotient.exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_normalized Q eA x)
  have hK : Nonempty ((Scheme.Modules.pullback z).obj K.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left) :=
    Quotient.exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_normalized Q eA y)
  have hH : Nonempty ((Scheme.Modules.pullback z).obj H.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left) :=
    Quotient.exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_normalized Q eA (x * y))
  have ht : (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf H) =
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor K)) :=
    h.trans (HilbertConstruction.Picard.SheafMonoid.toRelativePicard_mul A.scheme T (HilbertConstruction.Line.Bundles.LineBundle.classOf L) (HilbertConstruction.Line.Bundles.LineBundle.classOf K)).symm
  exact PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.class_eq_of_picard_eq A H (L.tensor K) hH.some
    (PullbackTensorFrame.algebraicPullbackTensorFrame z L.sheaf K.sheaf hL.some hK.some) ht

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterLineMultiplication
