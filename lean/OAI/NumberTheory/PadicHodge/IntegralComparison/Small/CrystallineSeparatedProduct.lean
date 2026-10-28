import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization

/-! # Crystalline Separated Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineSeparatedProduct

noncomputable section

/-!
# IntegralComparison: products in the small crystalline site over a separated scheme

The closed fibre product of affine opens of a separated X remains an affine
open. Thus the constructed big product is small, with the same universal
property, and the inclusion preserves binary products.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
variable (U V : Crystalline.Site.AffineThickening p B J δ f) (hp : 0 < p)

instance product_open : IsOpenImmersion
    (Crystalline.SeparatedProductGeometry.object f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp).mapToX := by
  let q : Spec (CommRingCat.of
      (Crystalline.SeparatedProductRing.Ring f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) ⧸
       Crystalline.SeparatedProductRing.ideal f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V))) ⟶
      Spec (CommRingCat.of (U.ring ⧸ U.ideal)) :=
    Crystalline.SeparatedProductGeometry.fstClosed f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V)
  have hv : IsOpenImmersion (BigCrystallineSite.fromSmall.obj V).mapToX := V.isOpenImmersion
  have hl : IsOpenImmersion
      (Crystalline.SeparatedProductData.closedFst f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V)) :=
    MorphismProperty.of_isPullback
      (Crystalline.SeparatedProductData.closed_pullback f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V)).flip hv
  have hq : IsOpenImmersion q := by
    change IsOpenImmersion (Crystalline.SeparatedProductGeometry.fstClosed f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V))
    rw [Crystalline.SeparatedProductGeometry.fstClosed_eq]
    have he : Spec.map (CommRingCat.ofHom (Spec.preimage
        (Crystalline.SeparatedProductData.closedFst f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V))).hom) =
        Crystalline.SeparatedProductData.closedFst f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) :=
      Spec.map_preimage _
    rw [he]
    infer_instance
  exact @IsOpenImmersion.comp _ _ _ q U.openMap hq U.isOpenImmersion

abbrev object : Crystalline.Site.AffineThickening p B J δ f :=
  CrystallineLocalization.smallOfBig
    (Crystalline.SeparatedProductGeometry.object f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp)

def fst : object f U V hp ⟶ U :=
  BigCrystallineSite.fromSmall.preimage (Crystalline.SeparatedProductGeometry.fst f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp)

def snd : object f U V hp ⟶ V :=
  BigCrystallineSite.fromSmall.preimage (Crystalline.SeparatedProductGeometry.snd f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp)

lemma map_fst : BigCrystallineSite.fromSmall.map (fst f U V hp) =
    Crystalline.SeparatedProductGeometry.fst f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp :=
  Functor.map_preimage _ _

lemma map_snd : BigCrystallineSite.fromSmall.map (snd f U V hp) =
    Crystalline.SeparatedProductGeometry.snd f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp :=
  Functor.map_preimage _ _

def fan : BinaryFan U V := BinaryFan.mk (fst f U V hp) (snd f U V hp)

def isProduct : IsLimit (fan f U V hp) := by
  apply isLimitOfReflectsOfMapIsLimit BigCrystallineSite.fromSmall
  rw [map_fst, map_snd]
  exact Crystalline.SeparatedProductLift.isProduct f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp

include hp in
lemma hasBinaryProduct : HasBinaryProduct U V := HasLimit.mk ⟨fan f U V hp, isProduct f U V hp⟩

include hp in
lemma inclusion_preserves_product : PreservesLimit (pair U V) BigCrystallineSite.fromSmall := by
  apply preservesLimit_of_preserves_limit_cone (isProduct f U V hp)
  refine (isLimitMapConeBinaryFanEquiv BigCrystallineSite.fromSmall (fst f U V hp) (snd f U V hp)).symm ?_
  rw [map_fst, map_snd]
  exact Crystalline.SeparatedProductLift.isProduct f (BigCrystallineSite.fromSmall.obj U) (BigCrystallineSite.fromSmall.obj V) hp

include hp in
omit U V in
lemma hasBinaryProducts : HasBinaryProducts (Crystalline.Site.AffineThickening p B J δ f) := by
  have (U V : Crystalline.Site.AffineThickening p B J δ f) : HasBinaryProduct U V :=
    hasBinaryProduct f U V hp
  exact hasBinaryProducts_of_hasLimit_pair _

include hp in
omit U V in
lemma inclusion_preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair)
    (BigCrystallineSite.fromSmall (p := p) (B := B) (J := J) (δ := δ) (f := f)) where
  preservesLimit {K} := by
    have := inclusion_preserves_product f (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩) hp
    exact preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineSeparatedProduct
