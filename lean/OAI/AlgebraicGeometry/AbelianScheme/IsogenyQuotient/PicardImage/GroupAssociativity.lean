import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupAssociativity.Construction

noncomputable section

/-! The image line products are associative on proper smooth connected
group parameters, by their common origin normalization. -/

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

variable {T : Over (Spec (.of k))} [GrpObj T]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalGroupProduct_associative
    (x y z xy yz w : T ⟶ C ⊗ B)
    [IsMonHom x] [IsMonHom y] [IsMonHom z] [IsMonHom xy] [IsMonHom yz] [IsMonHom w]
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) z, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x yz w hxw).app U m ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac y z yz hyz).app U n p) =
      (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac xy z w hzw).app U ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x y xy hxy).app U m n) p := by
  refine FiberAssociativity.Construction.fiberBilinear_associative_of_origin T (L) x y z xy yz w 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin y) (NormalizedProductOrigin.Construction.groupMap_origin z)
    (NormalizedProductOrigin.Construction.groupMap_origin xy) (NormalizedProductOrigin.Construction.groupMap_origin yz) (NormalizedProductOrigin.Construction.groupMap_origin w)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac y z yz hyz) (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x yz w hxw)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x y xy hxy) (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac xy z w hzw) ?_ U m n p
  intro V a b c
  simp only [ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin]
  exact FramedProductLaws.Construction.framedLineProduct_associative (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) V a b c

omit [IsMonHom q] in
theorem picardImageVerticalGroupProduct_associative
    (x y z xy yz w : T ⟶ C ⊗ B)
    [IsMonHom x] [IsMonHom y] [IsMonHom z] [IsMonHom xy] [IsMonHom yz] [IsMonHom w]
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) z, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x yz w hxw).app U m ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac y z yz hyz).app U n p) =
      (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac xy z w hzw).app U ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x y xy hxy).app U m n) p := by
  refine FiberAssociativity.Construction.fiberBilinear_associative_of_origin T (L) x y z xy yz w 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin y) (NormalizedProductOrigin.Construction.groupMap_origin z)
    (NormalizedProductOrigin.Construction.groupMap_origin xy) (NormalizedProductOrigin.Construction.groupMap_origin yz) (NormalizedProductOrigin.Construction.groupMap_origin w)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac y z yz hyz) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x yz w hxw)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x y xy hxy) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac xy z w hzw) ?_ U m n p
  intro V a b c
  simp only [ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin]
  exact FramedProductLaws.Construction.framedLineProduct_associative (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _) V a b c

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupAssociativity.Construction
