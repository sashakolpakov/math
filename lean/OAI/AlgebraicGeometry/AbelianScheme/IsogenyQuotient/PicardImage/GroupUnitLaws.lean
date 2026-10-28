import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.UnitFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupParameterUnitLaw
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupUnitLaws.Construction

noncomputable section

/-! Rigidity proves the image products' left unit laws on proper smooth
connected group parameters from their common origin normalization. -/

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

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
variable {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalGroupUnit_end
    (a x : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x x h) (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  apply GroupParameterUnitLaw.Construction.groupParameter_leftUnit_of_origin L a x
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x x h)
    (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
  · exact ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin D βv hβv βh hβh q i hfac a x x h
  · rw [UnitFrames.Construction.picardImageHorizontalUnitFrame_natural D βv hβv βh hβh q i hfac η[T] a 1 ha
      (MonObj.one_comp (fst C B)) (NormalizedProductOrigin.Construction.groupMap_origin a), UnitFrames.Construction.picardImageHorizontalUnitFrame_zero]

theorem picardImageHorizontalGroupUnit_left
    (a x : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x x h).app U
      ((UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageHorizontalGroupUnit_end D βv hβv βh hβh q i hfac a x ha h))

omit [IsMonHom q] in
theorem picardImageVerticalGroupUnit_end
    (a x : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a x x h) (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  apply GroupParameterUnitLaw.Construction.groupParameter_leftUnit_of_origin L a x
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a x x h)
    (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
  · exact ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin D βv hβv βh hβh q i hfac a x x h
  · rw [UnitFrames.Construction.picardImageVerticalUnitFrame_natural D βv hβv βh hβh q i hfac η[T] a 1 ha
      (MonObj.one_comp (snd C B)) (NormalizedProductOrigin.Construction.groupMap_origin a), UnitFrames.Construction.picardImageVerticalUnitFrame_zero]

omit [IsMonHom q] in
theorem picardImageVerticalGroupUnit_left
    (a x : T ⟶ C ⊗ B) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a x x h).app U
      ((UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageVerticalGroupUnit_end D βv hβv βh hβh q i hfac a x ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupUnitLaws.Construction
