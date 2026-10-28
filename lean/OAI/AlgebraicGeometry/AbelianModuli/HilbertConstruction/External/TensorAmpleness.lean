import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AmpleLineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductOpens
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionNonvanishingPullback

/-! # Tensor Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! External tensor products of ample line bundles are ample on fiber products over an affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y : Scheme.{u}}

def Line.Bundles.LineBundle.externalTensor (f : X ⟶ S) (g : Y ⟶ S) (L : Line.Bundles.LineBundle X) (M : Line.Bundles.LineBundle Y) :
    Line.Bundles.LineBundle (Limits.pullback f g) :=
  (L.pullback (pullback.fst f g)).tensor (M.pullback (pullback.snd f g))

theorem Line.Bundles.LineBundle.IsAmple.externalTensor [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) {L : Line.Bundles.LineBundle X} {M : Line.Bundles.LineBundle Y}
    (hL : L.IsAmple) (hM : M.IsAmple) : (Line.Bundles.LineBundle.externalTensor f g L M).IsAmple := by
  let : CompactSpace X := ⟨hL.1⟩
  let : CompactSpace Y := ⟨hM.1⟩
  have : QuasiCompact f := inferInstance
  have : CompactSpace (Limits.pullback f g : Scheme.{u}) := inferInstance
  apply (Line.Bundles.LineBundle.externalTensor f g L M).isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨a, ha, s, hxs, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 (pullback.fst f g x)
  obtain ⟨b, hb, t, hxt, ht⟩ := (M.isAmple_iff_tensorPower.mp hM).2 (pullback.snd f g x)
  let eL := (L.tensorPowerComposeIso b a).symm
  let eM := (M.tensorPowerComposeIso a b).symm ≪≫
    eqToIso (congrArg (fun d => (M.tensorPower d).sheaf) (Nat.mul_comm a b))
  let s' : Line.Bundles.structureModule X ⟶ (L.tensorPower (b * a)).sheaf := TensorPower.Maps.tensorPowerSection s b ≫ eL.hom
  let t' : Line.Bundles.structureModule Y ⟶ (M.tensorPower (b * a)).sheaf := TensorPower.Maps.tensorPowerSection t a ≫ eM.hom
  have hs' : Ample.LineBundles.sectionNonvanishing s' = Ample.LineBundles.sectionNonvanishing s :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ eL).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower a) s b hb)
  have ht' : Ample.LineBundles.sectionNonvanishing t' = Ample.LineBundles.sectionNonvanishing t :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ eM).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := M.tensorPower b) t a ha)
  let A := L.pullback (pullback.fst f g)
  let B := M.pullback (pullback.snd f g)
  let u := Power.SectionNonvanishingPullback.pullbackPowerSection (pullback.fst f g) L (b * a) s'
  let v := Power.SectionNonvanishingPullback.pullbackPowerSection (pullback.snd f g) M (b * a) t'
  have hu : Ample.LineBundles.sectionNonvanishing u = pullback.fst f g ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s :=
    (Power.SectionNonvanishingPullback.pullbackPowerSection_nonvanishing (pullback.fst f g) L (b * a) s').trans
      (congrArg (fun W => pullback.fst f g ⁻¹ᵁ W) hs')
  have hv : Ample.LineBundles.sectionNonvanishing v = pullback.snd f g ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing t :=
    (Power.SectionNonvanishingPullback.pullbackPowerSection_nonvanishing (pullback.snd f g) M (b * a) t').trans
      (congrArg (fun W => pullback.snd f g ⁻¹ᵁ W) ht')
  let w : Line.Bundles.structureModule (Limits.pullback f g) ⟶ ((Line.Bundles.LineBundle.externalTensor f g L M).tensorPower (b * a)).sheaf :=
    Tensor.ProductSections.tensorProductSection u v ≫ (A.tensorPowerTensorIso B (b * a)).inv
  have hw : Ample.LineBundles.sectionNonvanishing w =
      (pullback.fst f g ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s) ⊓ (pullback.snd f g ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing t) :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ (A.tensorPowerTensorIso B (b * a)).symm).trans
      ((Tensor.SectionNonvanishing.sectionNonvanishing_tensorProduct (A.tensorPower (b * a)) (B.tensorPower (b * a)) u v).trans
        (congrArg₂ (fun U V : (Limits.pullback f g).Opens => U ⊓ V) hu hv))
  exact ⟨b * a, Nat.mul_pos hb ha, w, hw.symm ▸ ⟨hxs, hxt⟩,
    hw.symm ▸ Affine.ProductOpens.affine_product_open f g (Ample.LineBundles.sectionNonvanishing s) (Ample.LineBundles.sectionNonvanishing t) hs ht⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
