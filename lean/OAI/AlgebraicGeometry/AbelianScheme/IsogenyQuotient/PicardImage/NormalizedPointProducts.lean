import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.PointProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPointFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductIsomorphisms

/-! # Normalized Point Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.NormalizedPointProducts.Construction

noncomputable section

/-! The actual Picard-image point products have unique normalizations
at the origin of a proper smooth connected group parameter. -/

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

local instance imagePointMapMul_isMonHom {X Y : Over (Spec (.of k))}
    [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (a b : X ⟶ Y) [IsMonHom a] [IsMonHom b] :
    IsMonHom (a * b) := by
  rw [Hom.mul_def]
  infer_instance

def picardImagePointOriginFrame (x : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).pullback η[T].left).sheaf :=
  RigidifiedPointFrames.Construction.rigidifiedPointOriginFrame (ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac) x a

theorem existsUnique_picardImagePointProduct_left
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    ∃! e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac y a).sheaf ≅
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac (x * y) a).sheaf,
      (Scheme.Modules.pullback η[T].left).mapIso e = Poincare.ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac y a)
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac (x * y) a) := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[T].left
    ((PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).tensor
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac y a))
    (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac (x * y) a)
    (Classical.choice (PointProducts.Construction.picardImagePointLine_tensor_left D βv hβv βh hβh q i hfac x y a)) _

omit [IsMonHom q] [IsCommMonObj C] in
theorem existsUnique_picardImagePointProduct_right
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    ∃! e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x b).sheaf ≅
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x (a * b)).sheaf,
      (Scheme.Modules.pullback η[T].left).mapIso e = Poincare.ProductIsomorphisms.Construction.lineTensorFrameComparison η[T].left _ _ _
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac x a)
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac x b)
        (picardImagePointOriginFrame D βv hβv βh hβh q i hfac x (a * b)) := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[T].left
    ((PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).tensor
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x b))
    (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x (a * b))
    (Classical.choice (PointProducts.Construction.picardImagePointLine_tensor_right D βv hβv βh hβh q i hfac x a b)) _

def normalizedPicardImagePointProduct_left
    (x y : T ⟶ C) (a : T ⟶ B) [IsMonHom x] [IsMonHom y] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac y a).sheaf ≅
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac (x * y) a).sheaf :=
  Classical.choose (existsUnique_picardImagePointProduct_left D βv hβv βh hβh q i hfac x y a)

def normalizedPicardImagePointProduct_right
    (x : T ⟶ C) (a b : T ⟶ B) [IsMonHom x] [IsMonHom a] [IsMonHom b] :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x a).sheaf
      (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x b).sheaf ≅
        (PointProducts.Construction.picardImagePointLine D βv hβv βh hβh q i hfac x (a * b)).sheaf :=
  Classical.choose (existsUnique_picardImagePointProduct_right D βv hβv βh hβh q i hfac x a b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.NormalizedPointProducts.Construction
