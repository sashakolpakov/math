import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.LineProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts

/-! # Horizontal Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalProduct.Construction

noncomputable section

/-! The original Poincare bundle constructs its horizontal product
on all test schemes. The normalized universal product is pulled back
along the actual triple of coordinates. No product is supplied as input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

abbrev poincareHorizontalParameter : Over (Spec (.of k)) :=
  (D.abelian.scheme ⊗ D.abelian.scheme) ⊗ A.scheme

local instance horizontalParameter_smooth : Smooth (poincareHorizontalParameter D).hom := by
  have : Smooth (D.abelian.scheme ⊗ D.abelian.scheme).hom := by dsimp; infer_instance
  dsimp [poincareHorizontalParameter]
  infer_instance

local instance horizontalParameter_proper : IsProper (poincareHorizontalParameter D).hom := by
  have : IsProper (D.abelian.scheme ⊗ D.abelian.scheme).hom := by dsimp; infer_instance
  dsimp [poincareHorizontalParameter]
  infer_instance

local instance horizontalParameter_connected : GeometricallyConnected (poincareHorizontalParameter D).hom := by
  have : GeometricallyConnected (D.abelian.scheme ⊗ D.abelian.scheme).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst D.abelian.scheme.hom D.abelian.scheme.hom)
      D.abelian.scheme.hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst (D.abelian.scheme ⊗ D.abelian.scheme).hom A.scheme.hom)
    (D.abelian.scheme ⊗ D.abelian.scheme).hom

local instance horizontalParameter_compact : CompactSpace (poincareHorizontalParameter D).left :=
  QuasiCompact.compactSpace_of_compactSpace (poincareHorizontalParameter D).hom

local instance horizontalParameter_quasiSeparated : QuasiSeparatedSpace (poincareHorizontalParameter D).left :=
  quasiSeparatedSpace_of_quasiSeparated (poincareHorizontalParameter D).hom

/-- The actual global bilinear product, uniquely normalized by the original Poincare zero frame. -/
def poincareGlobalHorizontalProduct :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft D.abelian.scheme A.scheme))
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight D.abelian.scheme A.scheme))
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint D.abelian.scheme A.scheme)) :=
  BilinearProducts.Construction.normalizedPoincareBilinearLeft D
    (fst (D.abelian.scheme ⊗ D.abelian.scheme) A.scheme ≫ fst D.abelian.scheme D.abelian.scheme)
    (fst (D.abelian.scheme ⊗ D.abelian.scheme) A.scheme ≫ snd D.abelian.scheme D.abelian.scheme)
    (snd (D.abelian.scheme ⊗ D.abelian.scheme) A.scheme)

instance poincareGlobalHorizontalProduct_isIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (poincareGlobalHorizontalProduct D)) :=
  BilinearProducts.Construction.normalizedPoincareBilinearLeft_isIso D _ _ _

/-- Multiplication of actual Poincare fibers on an arbitrary test scheme. -/
def poincareHorizontalProduct {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a) (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) b)
      (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) c) :=
  Universal.LineProducts.Construction.lineProductFromUniversal (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareGlobalHorizontalProduct D) a b c h

instance poincareHorizontalProduct_isIso {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a b c) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (poincareHorizontalProduct D a b c h)) :=
  Universal.LineProducts.Construction.lineProductFromUniversal_isIso _ _ a b c h

theorem poincareHorizontalProduct_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a b c)
    (a' b' c' : U ⟶ D.abelian.scheme ⊗ A.scheme)
    (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a' b' c')
    (ha : r ≫ a = a') (hb : r ≫ b = b') (hc : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r a b c a' b' c' ha hb hc (poincareHorizontalProduct D a b c h) =
      poincareHorizontalProduct D a' b' c' h' :=
  Universal.LineProducts.Construction.lineProductFromUniversal_natural _ _ r a b c h a' b' c' h' ha hb hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalProduct.Construction
