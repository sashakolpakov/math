import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAxisFrame

/-! # Unit Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.UnitFrames.Construction

noncomputable section

/-! Both image-line unit frames commute with all test-scheme changes
and agree with the common zero frame. -/

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

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)
open OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

def picardImageHorizontalUnitFrame {T : Over (Spec (.of k))} (a : T ⟶ C ⊗ B)
    (ha : a ≫ fst C B = 1) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L a :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C)) L
    (HorizontalAxisFrame.Construction.picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) (a ≫ snd C B) a (by
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [HorizontalAxisFrame.Construction.picardImageHorizontalAxis, Category.assoc, lift_fst, MonObj.comp_one] using ha.symm
      · simp only [HorizontalAxisFrame.Construction.picardImageHorizontalAxis, Category.assoc, lift_snd, Category.comp_id])

def picardImageVerticalUnitFrame {T : Over (Spec (.of k))} (a : T ⟶ C ⊗ B)
    (ha : a ≫ snd C B = 1) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L a :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (lift (𝟙 C) (1 : C ⟶ B)) L (Q).axis.symm (a ≫ fst C B) a (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id]
    · simpa only [Category.assoc, lift_snd, MonObj.comp_one] using ha.symm)

theorem picardImageHorizontalUnitFrame_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a : T ⟶ C ⊗ B) (a' : U ⟶ C ⊗ B)
    (ha : a ≫ fst C B = 1) (ha' : a' ≫ fst C B = 1) (hr : r ≫ a = a') :
    Picard.PoincareBundle.Line.Fibers.pullSection L r a a' hr (picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      (picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a' ha').hom :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_section_natural (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C)) L
    (HorizontalAxisFrame.Construction.picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) r (a ≫ snd C B) a _ (a' ≫ snd C B) a' _
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ snd C B) hr)) hr

omit [IsMonHom q] [GrpObj C] [IsCommMonObj C] in
theorem picardImageVerticalUnitFrame_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a : T ⟶ C ⊗ B) (a' : U ⟶ C ⊗ B)
    (ha : a ≫ snd C B = 1) (ha' : a' ≫ snd C B = 1) (hr : r ≫ a = a') :
    Picard.PoincareBundle.Line.Fibers.pullSection L r a a' hr (picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      (picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a' ha').hom :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_section_natural (lift (𝟙 C) (1 : C ⟶ B)) L (Q).axis.symm
    r (a ≫ fst C B) a _ (a' ≫ fst C B) a' _
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ fst C B) hr)) hr

theorem picardImageHorizontalAxisFrame_at_zero (T : Over (Spec (.of k))) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C)) L
      (HorizontalAxisFrame.Construction.picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) (1 : T ⟶ B) 1
      (MonObj.one_comp (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C))) = RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q T := by
  have h := Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C)) L
    (HorizontalAxisFrame.Construction.picardImageHorizontalAxisFrame D βv hβv βh hβh q i hfac) (toUnit T) η[B] 1
    (HorizontalAxisFrame.Construction.picardImageHorizontalAxis_origin (B := B) (C := C)) (1 : T ⟶ B) 1
    (MonObj.one_comp (HorizontalAxisFrame.Construction.picardImageHorizontalAxis (B := B) (C := C))) rfl (MonObj.comp_one (toUnit T))
  rw [HorizontalAxisFrame.Construction.picardImageHorizontalAxisFrame_at_origin] at h
  exact h.symm.trans (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame_natural Q (toUnit T))

theorem picardImageHorizontalUnitFrame_zero (T : Over (Spec (.of k))) :
    picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac (1 : T ⟶ C ⊗ B)
      (MonObj.one_comp (fst C B)) = RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q T := by
  simpa only [picardImageHorizontalUnitFrame, MonObj.one_comp] using
    picardImageHorizontalAxisFrame_at_zero D βv hβv βh hβh q i hfac T

omit [IsMonHom q] in
theorem picardImageVerticalUnitFrame_zero (T : Over (Spec (.of k))) :
    picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac (1 : T ⟶ C ⊗ B)
      (MonObj.one_comp (snd C B)) = RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q T := by
  unfold picardImageVerticalUnitFrame RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame
  simp only [MonObj.one_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.UnitFrames.Construction
