import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Poincare Fixed -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixed

noncomputable section

/-! Put the original Poincare line on the already descended abelian
family, retaining the original dual cover as parameter. Its homogeneity
and zero normalization are transported by actual scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S T : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g T}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S)
    (e : A.scheme ≅ (B.pullback u).scheme) [IsMonHom e.hom]

def fixedFamilyPoincare : HilbertConstruction.Line.Bundles.LineBundle (((Over.map u).obj D.abelian.scheme) ⊗ B.scheme).left :=
  HilbertConstruction.Line.Bundles.LineBundle.pullback (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme).inv
    (D.familyTransportPoincare e)

theorem fixedFamilyPoincare_homogeneous :
    B.IsHomogeneousPicardClass ((Over.map u).obj D.abelian.scheme)
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (fixedFamilyPoincare D B u e)) :=
  B.isHomogeneousPicardClass_baseChange u D.abelian.scheme
    (HilbertConstruction.Line.Bundles.LineBundle.classOf (D.familyTransportPoincare e)) (D.familyTransportPoincare_homogeneous e)

def fixedFamilyPoincare_zeroIso :
    (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B ((Over.map u).obj D.abelian.scheme)).left
      (fixedFamilyPoincare D B u e)).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelian.scheme.left :=
  (Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero B ((Over.map u).obj D.abelian.scheme)).left
    (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme).inv).app (D.familyTransportPoincare e).sheaf ≪≫
  (Scheme.Modules.pullbackCongr (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.familyBaseChangeIso_zero_inv B u D.abelian.scheme)).app
    (D.familyTransportPoincare e).sheaf ≪≫ (D.familyTransportPoincare_abelianZero e).some

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixed
