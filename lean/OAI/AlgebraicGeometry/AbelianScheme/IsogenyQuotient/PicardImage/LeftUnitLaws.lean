import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.UnitParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitLawPullback

/-! # Left Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.LeftUnitLaws.Construction

noncomputable section

/-! The constructed image products satisfy their left unit laws on
every test scheme by pullback from the universal unit configurations. -/

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
local instance imageProductSpace_smooth : Smooth (C ⊗ B).hom := by dsimp; infer_instance
local instance imageProductSpace_proper : IsProper (C ⊗ B).hom := by dsimp; infer_instance
local instance imageProductSpace_connected : GeometricallyConnected (C ⊗ B).hom :=
  GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst C.hom B.hom) C.hom
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalUnit_end {T : Over (Spec (.of k))}
    (a x : T ⟶ (C ⊗ B)) (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x x h) (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  have hf := Product.UnitParameters.Construction.productHorizontalUnitParameter_factor C B a x ha h
  have hu := GroupUnitLaws.Construction.picardImageHorizontalGroupUnit_end D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 ((C ⊗ B)))
    (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B) (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B)
  have hp := UnitLawPullback.Construction.contractedUnit_pullback (L) x
    (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 ((C ⊗ B))) a x hf (Category.comp_id x)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 _) (𝟙 _) (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B))
    (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B)).hom hu
  rw [ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 _) (𝟙 _)
      (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B) a x x h hf (Category.comp_id x) (Category.comp_id x),
    UnitFrames.Construction.picardImageHorizontalUnitFrame_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) a
      (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B) ha hf] at hp
  exact hp

theorem picardImageHorizontalProduct_unit_left {T : Over (Spec (.of k))}
    (a x : T ⟶ (C ⊗ B)) (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x x h).app U
      ((UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans (congrArg (fun f => f.app U m) (picardImageHorizontalUnit_end D βv hβv βh hβh q i hfac a x ha h))

omit [IsMonHom q] in
theorem picardImageVerticalUnit_end {T : Over (Spec (.of k))}
    (a x : T ⟶ (C ⊗ B)) (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a x x h) (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  have hf := Product.UnitParameters.Construction.productVerticalUnitParameter_factor C B a x ha h
  have hu := GroupUnitLaws.Construction.picardImageVerticalGroupUnit_end D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 ((C ⊗ B)))
    (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B) (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B)
  have hp := UnitLawPullback.Construction.contractedUnit_pullback (L) x
    (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 ((C ⊗ B))) a x hf (Category.comp_id x)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 _) (𝟙 _) (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B))
    (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B)).hom hu
  rw [ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 _) (𝟙 _)
      (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B) a x x h hf (Category.comp_id x) (Category.comp_id x),
    UnitFrames.Construction.picardImageVerticalUnitFrame_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productVerticalUnitParameter C B) a
      (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B) ha hf] at hp
  exact hp

omit [IsMonHom q] in
theorem picardImageVerticalProduct_unit_left {T : Over (Spec (.of k))}
    (a x : T ⟶ (C ⊗ B)) (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a x x h).app U
      ((UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans (congrArg (fun f => f.app U m) (picardImageVerticalUnit_end D βv hβv βh hβh q i hfac a x ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.LeftUnitLaws.Construction
