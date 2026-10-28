import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf

/-! # Picard Commutative Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeComposition.Construction

noncomputable section

/-! Composition for pullback on the actual commutative Picard sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g h d : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (f : A.scheme ⟶ B.scheme) (a : B.scheme ⟶ C.scheme) [IsMonHom f] [IsMonHom a]

theorem picardPullbackPresheaf_comp :
    Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf A C (f ≫ a) =
      Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf B C a ≫ Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf A B f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro c
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ (f ≫ a)).left c.val =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ a).left c.val)
  rw [whiskerLeft_comp, Over.comp_left]
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp _ _ _

theorem picardPullbackSheaf_comp :
    Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A C (f ≫ a) =
      Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B C a ≫ Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f := by
  change (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map _ = _
  rw [picardPullbackPresheaf_comp, Functor.map_comp]
  rfl

theorem homogeneousPicardFppfPullback_comp :
    PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A C (f ≫ a) =
      PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B C a ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  change Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom A C (f ≫ a) T.unop c =
    Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom A B f T.unop (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom B C a T.unop c)
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg
      (fun z : C.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf => z.hom)
      (picardPullbackSheaf_comp A B C f a)) T) c
  have hr := (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply A B f T.unop
      (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom B C a T.unop c)).trans
    (congrArg ((Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.app T)
      (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply B C a T.unop c))
  exact (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply A C (f ≫ a) T.unop c).trans (hh.trans hr.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeComposition.Construction
