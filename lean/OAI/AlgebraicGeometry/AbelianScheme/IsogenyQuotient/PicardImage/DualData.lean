import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageHomogeneity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageAxes
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageOrigin
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.DualData.Construction

noncomputable section

/-! The actual Picard image and its normalized line give the full
dual abelian data once the image map has been proved an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

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

variable [GrpObj C] [IsCommMonObj C] [IsMonHom q]
  [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom] [IsIso i]

set_option backward.isDefEq.respectTransparency false in
def picardImageDualData : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B where
  abelian := C
  group := inferInstance
  commutative := inferInstance
  proper := inferInstance
  smooth := inferInstance
  connected := inferInstance
  representable := (Functor.RepresentableBy.equivUliftYonedaIso (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj C).symm (asIso i)
  origin T := ProductPicard.ImageOrigin.Construction.productPicardImage_origin (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh q i hfac T
  poincare := ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac
  poincareHomogeneous := ProductPicard.ImageHomogeneity.Construction.normalizedProductPicardImageLine_homogeneous D βv hβv βh hβh q i hfac
  universalClass := ProductPicard.ImageHomogeneity.Construction.normalizedProductPicardImageLine_native_universal_class D βv hβv βh hβh q i hfac
  normalizedAtAbelianZero := ⟨ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine_axis D βv hβv βh hβh q i hfac⟩
  normalizedAtDualZero := ⟨ProductPicard.ImageAxes.Construction.normalizedProductPicardImageLine_secondAxis D βv hβv βh hβh q i hfac⟩

theorem picardImageDualData_value (T : Over (Spec (.of k))) (x : T ⟶ C) :
    (picardImageDualData D βv hβv βh hβh q i hfac).representable.homEquiv x =
      i.app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.DualData.Construction
