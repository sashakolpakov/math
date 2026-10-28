import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Closed Family Intrinsic Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback

noncomputable section

/-! The geometric inverse-image family in relative projective space
recovers the native categorical pullback compatibly with the precise
projective-presentation base-change embedding. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comp_comparison_inv {C : Type*} [Category C]
    {W X Y Z : C} (e : Y ≅ Z) (p : W ⟶ X) (q : X ⟶ Z) (r : W ⟶ Y)
    (h : p ≫ q = r ≫ e.hom) : p ≫ (q ≫ e.inv) = r := by
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem functorReturnMap_comp
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Z W : D} (j : X ⟶ Y) (k : Z ≅ F.obj Y)
    (a : W ⟶ F.obj X) (b : W ⟶ Z) (h : a ≫ F.map j = b ≫ k.hom) :
    a ≫ CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap F j k = b := by
  unfold CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem pullbackAlongIso_embedding {S T : Scheme.{u}} {P : Over S} {Q : Over T}
    (F : Closed.Families.FlatClosedFamily P) (p : Q.left ⟶ P.left) (f : T ⟶ S)
    (hp : IsPullback p Q.hom P.hom f)
    (e : Q ≅ (Over.pullback f).obj P) (he : ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp = e) :
    (F.pullbackAlongIso p f hp).hom ≫
      CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback f) F.inclusion e =
      (F.pullbackAlong p f hp).inclusion :=
  functorReturnMap_comp (Over.pullback f) F.inclusion e _ _
    ((F.pullbackAlongIso_inclusion p f hp).trans
    (congrArg (fun z => (F.pullbackAlong p f hp).inclusion ≫ z.hom) he))

theorem relativeProjectiveCartesianIso_eq_native
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n) =
      SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n).isoPullback_hom_fst.trans
      (BaseChangeIsoProjections.projectiveSpaceOverBaseChangeIso_hom_fst f n).symm
  · exact (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n)).hom.w.trans
        (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).hom.w.symm

variable {S T : Scheme.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (ProjectivePresentations.projectiveSpaceOver S n)) (f : T ⟶ S)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily.projectiveBaseChangeSchemeIso :
    (F.projectiveBaseChange f).scheme ≅ (Over.pullback f).obj F.scheme :=
  F.pullbackAlongIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n)

/-- The inverse-image comparison identifies the native base-change embedding. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily.projectiveBaseChangeSchemeIso_embedding :
    (F.projectiveBaseChangeSchemeIso f).hom ≫
      CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback f) F.inclusion
        (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n) = (F.projectiveBaseChange f).inclusion := by
  convert (pullbackAlongIso_embedding F (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n) (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n)
    (relativeProjectiveCartesianIso_eq_native f n)) using 2 <;> rfl

theorem relativeHilbertFamily_eqSchemeIso_inclusion {S : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    {F G : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P} (h : F = G) :
    (eqToIso (congrArg (fun H : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P => H.family.scheme) h)).hom ≫
      G.family.inclusion = F.family.inclusion := by
  cases h
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback
