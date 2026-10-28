import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Quotient Difference Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceNormalization

noncomputable section

/-! The zero section in the quotient coordinate lifts through the
product isogeny, and therefore retains the actual normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem productIsogeny_zeroSlice :
    lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) =
      lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

def quotientDifference_dualZeroIso (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left)
    (e : (Q.pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅ (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf) :
    (Q.pullback (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (productIsogeny_zeroSlice p)).symm).app Q.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left
      (p.hom ⊗ₘ 𝟙 A.scheme).left).app Q.sheaf).symm ≪≫
    (Scheme.Modules.pullback (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left).mapIso e ≪≫
    (AbelianDifferenceBundle.abelianDifferenceBundle_normalized_right A L).some

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceNormalization
