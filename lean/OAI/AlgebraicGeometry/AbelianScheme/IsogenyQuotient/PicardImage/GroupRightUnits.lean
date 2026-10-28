import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterRightUnitLaw

/-! # Group Right Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupRightUnits.Construction

noncomputable section

/-! Both image products satisfy their right unit laws on proper smooth
connected group parameters by the common origin normalization. -/

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
theorem picardImageHorizontalGroupRightUnit_end
    (x a : T ⟶ C ⊗ B) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x a x) :
    RightContraction.Construction.lineContractRight (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x a x h) (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  apply ParameterRightUnitLaw.Construction.groupParameter_rightUnit_of_origin L x a
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x a x h)
    (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
  · exact ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin D βv hβv βh hβh q i hfac x a x h
  · rw [UnitFrames.Construction.picardImageHorizontalUnitFrame_natural D βv hβv βh hβh q i hfac η[T] a 1 ha
      (MonObj.one_comp (fst C B)) (NormalizedProductOrigin.Construction.groupMap_origin a), UnitFrames.Construction.picardImageHorizontalUnitFrame_zero]

theorem picardImageHorizontalGroupUnit_right
    (x a : T ⟶ C ⊗ B) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x a x h).app U m
      ((UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageHorizontalGroupRightUnit_end D βv hβv βh hβh q i hfac x a ha h))

omit [IsMonHom q] in
theorem picardImageVerticalGroupRightUnit_end
    (x a : T ⟶ C ⊗ B) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x a x) :
    RightContraction.Construction.lineContractRight (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x a x h) (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  apply ParameterRightUnitLaw.Construction.groupParameter_rightUnit_of_origin L x a
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x a x h)
    (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha) (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
  · exact ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin D βv hβv βh hβh q i hfac x a x h
  · rw [UnitFrames.Construction.picardImageVerticalUnitFrame_natural D βv hβv βh hβh q i hfac η[T] a 1 ha
      (MonObj.one_comp (snd C B)) (NormalizedProductOrigin.Construction.groupMap_origin a), UnitFrames.Construction.picardImageVerticalUnitFrame_zero]

omit [IsMonHom q] in
theorem picardImageVerticalGroupUnit_right
    (x a : T ⟶ C ⊗ B) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x a x h).app U m
      ((UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageVerticalGroupRightUnit_end D βv hβv βh hβh q i hfac x a ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupRightUnits.Construction
