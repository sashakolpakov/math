import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.VerticalProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts

/-! # Vertical Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalProduct.Construction

noncomputable section

/-! The original Poincare bundle constructs its vertical bilinear
product on every test scheme, in the original dual-times-abelian order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

abbrev poincareVerticalParameter : Over (Spec (.of k)) :=
  (A.scheme ⊗ A.scheme) ⊗ D.abelian.scheme

local instance verticalParameter_smooth : Smooth (poincareVerticalParameter D).hom := by
  have : Smooth (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  dsimp [poincareVerticalParameter]
  infer_instance

local instance verticalParameter_proper : IsProper (poincareVerticalParameter D).hom := by
  have : IsProper (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  dsimp [poincareVerticalParameter]
  infer_instance

local instance verticalParameter_connected : GeometricallyConnected (poincareVerticalParameter D).hom := by
  have : GeometricallyConnected (A.scheme ⊗ A.scheme).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst A.scheme.hom A.scheme.hom) A.scheme.hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst (A.scheme ⊗ A.scheme).hom D.abelian.scheme.hom)
    (A.scheme ⊗ A.scheme).hom

local instance verticalParameter_compact : CompactSpace (poincareVerticalParameter D).left :=
  QuasiCompact.compactSpace_of_compactSpace (poincareVerticalParameter D).hom

local instance verticalParameter_quasiSeparated : QuasiSeparatedSpace (poincareVerticalParameter D).left :=
  quasiSeparatedSpace_of_quasiSeparated (poincareVerticalParameter D).hom

def poincareGlobalVerticalProduct :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) Universal.VerticalProducts.Construction.verticalInputLeft)
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) Universal.VerticalProducts.Construction.verticalInputRight)
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) Universal.VerticalProducts.Construction.verticalOutputPoint) :=
  BilinearProducts.Construction.normalizedPoincareBilinearRight D (snd (A.scheme ⊗ A.scheme) D.abelian.scheme)
    (fst (A.scheme ⊗ A.scheme) D.abelian.scheme ≫ fst A.scheme A.scheme)
    (fst (A.scheme ⊗ A.scheme) D.abelian.scheme ≫ snd A.scheme A.scheme)

instance poincareGlobalVerticalProduct_isIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (poincareGlobalVerticalProduct D)) :=
  BilinearProducts.Construction.normalizedPoincareBilinearRight_isIso D _ _ _

def poincareVerticalProduct {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a) (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) b)
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) c) :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareGlobalVerticalProduct D) a b c h

instance poincareVerticalProduct_isIso {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a b c) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (poincareVerticalProduct D a b c h)) :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal_isIso _ _ a b c h

theorem poincareVerticalProduct_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a b c)
    (a' b' c' : U ⟶ D.abelian.scheme ⊗ A.scheme)
    (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a' b' c')
    (ha : r ≫ a = a') (hb : r ≫ b = b') (hc : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r a b c a' b' c' ha hb hc (poincareVerticalProduct D a b c h) =
      poincareVerticalProduct D a' b' c' h' :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal_natural _ _ r a b c h a' b' c' h' ha hb hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalProduct.Construction
