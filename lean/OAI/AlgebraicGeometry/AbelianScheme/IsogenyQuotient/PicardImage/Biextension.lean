import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Interchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Multiplications
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Biextension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Biextension.Construction

noncomputable section

/-! The actual image multiplications satisfy the full PoincareBundle interchange
predicate on all test schemes. -/

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

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageMultiplications_interchange :
    Picard.PoincareBundle.Biextension.Compatibility.Interchange (L)
      (Multiplications.Construction.picardImageHorizontalMultiplication D βv hβv βh hβh q i hfac)
      (Multiplications.Construction.picardImageVerticalMultiplication D βv hβv βh hβh q i hfac) := by
  intro T
  exact Interchange.Construction.picardImageProducts_interchange D βv hβv βh hβh q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Biextension.Construction
