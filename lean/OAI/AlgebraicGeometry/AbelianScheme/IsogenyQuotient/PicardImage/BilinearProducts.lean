import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.NormalizedPointProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts

/-! # Bilinear Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearProducts.Construction

noncomputable section

/-! The normalized actual image-line tensor products give bilinear
sheaf products whose restrictions to the origin multiply the fixed frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C]
  {T : Over (Spec (.of k))} [GrpObj T] [IsLocallyNoetherian T.left]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

attribute [local instance] NormalizedPointProducts.Construction.imagePointMapMul_isMonHom

theorem normalizedPicardImagePointProduct_left_origin
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    (Scheme.Modules.pullback η[T].left).mapIso
      (NormalizedPointProducts.Construction.normalizedPicardImagePointProduct_left D βv hβv βh hβh q i hfac x y a) =
        Poincare.ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac y a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac (x * y) a) :=
  (Classical.choose_spec (NormalizedPointProducts.Construction.existsUnique_picardImagePointProduct_left D βv hβv βh hβh q i hfac x y a)).1

omit [IsMonHom q] [IsCommMonObj C] in
theorem normalizedPicardImagePointProduct_right_origin
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    (Scheme.Modules.pullback η[T].left).mapIso
      (NormalizedPointProducts.Construction.normalizedPicardImagePointProduct_right D βv hβv βh hβh q i hfac x a b) =
        Poincare.ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x b)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x (a * b)) :=
  (Classical.choose_spec (NormalizedPointProducts.Construction.existsUnique_picardImagePointProduct_right D βv hβv βh hβh q i hfac x a b)).1

def normalizedPicardImageBilinearLeft
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac y a).sheaf
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac (x * y) a).sheaf :=
  Poincare.BilinearProducts.Construction.bilinearOfLineIso (NormalizedPointProducts.Construction.normalizedPicardImagePointProduct_left D βv hβv βh hβh q i hfac x y a)

instance normalizedPicardImageBilinearLeft_isIso
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (normalizedPicardImageBilinearLeft D βv hβv βh hβh q i hfac x y a)) :=
  Poincare.BilinearProducts.Construction.bilinearOfLineIso_isIso _

theorem normalizedPicardImageBilinearLeft_origin
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left
      (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a))
      (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac y a))
      (normalizedPicardImageBilinearLeft D βv hβv βh hβh q i hfac x y a) =
        Poincare.BilinearProducts.Construction.framedLineProduct (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac y a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac (x * y) a) :=
  Poincare.BilinearProducts.Construction.normalizedLineProduct_pullback η[T].left _ _ _ _ _ _ _
    (normalizedPicardImagePointProduct_left_origin D βv hβv βh hβh q i hfac x y a)

def normalizedPicardImageBilinearRight
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x b).sheaf
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x (a * b)).sheaf :=
  Poincare.BilinearProducts.Construction.bilinearOfLineIso (NormalizedPointProducts.Construction.normalizedPicardImagePointProduct_right D βv hβv βh hβh q i hfac x a b)

instance normalizedPicardImageBilinearRight_isIso
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (normalizedPicardImageBilinearRight D βv hβv βh hβh q i hfac x a b)) :=
  Poincare.BilinearProducts.Construction.bilinearOfLineIso_isIso _

omit [IsMonHom q] [IsCommMonObj C] in
theorem normalizedPicardImageBilinearRight_origin
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left
      (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a))
      (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x b))
      (normalizedPicardImageBilinearRight D βv hβv βh hβh q i hfac x a b) =
        Poincare.BilinearProducts.Construction.framedLineProduct (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x b)
          (NormalizedPointProducts.Construction.picardImagePointOriginFrame D βv hβv βh hβh q i hfac x (a * b)) :=
  Poincare.BilinearProducts.Construction.normalizedLineProduct_pullback η[T].left _ _ _ _ _ _ _
    (normalizedPicardImagePointProduct_right_origin D βv hβv βh hβh q i hfac x a b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.BilinearProducts.Construction
