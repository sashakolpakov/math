import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Gluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Ample Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor products of ample line bundles on schemes with affine diagonal are ample. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M : Line.Bundles.LineBundle X}

theorem Line.Bundles.LineBundle.IsAmple.tensor [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple := by
  apply (L.tensor M).isAmple_iff_tensorPower.mpr
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨a, ha, s, hxs, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 x
  obtain ⟨b, hb, t, hxt, ht⟩ := (M.isAmple_iff_tensorPower.mp hM).2 x
  let eL := (L.tensorPowerComposeIso b a).symm
  let eM := (M.tensorPowerComposeIso a b).symm ≪≫
    eqToIso (congrArg (fun d => (M.tensorPower d).sheaf) (Nat.mul_comm a b))
  let s' : Line.Bundles.structureModule X ⟶ (L.tensorPower (b * a)).sheaf := TensorPower.Maps.tensorPowerSection s b ≫ eL.hom
  let t' : Line.Bundles.structureModule X ⟶ (M.tensorPower (b * a)).sheaf := TensorPower.Maps.tensorPowerSection t a ≫ eM.hom
  have hs' : Ample.LineBundles.sectionNonvanishing s' = Ample.LineBundles.sectionNonvanishing s :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ eL).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower a) s b hb)
  have ht' : Ample.LineBundles.sectionNonvanishing t' = Ample.LineBundles.sectionNonvanishing t :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ eM).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := M.tensorPower b) t a ha)
  let w : Line.Bundles.structureModule X ⟶ ((L.tensor M).tensorPower (b * a)).sheaf :=
    Tensor.ProductSections.tensorProductSection s' t' ≫ (L.tensorPowerTensorIso M (b * a)).inv
  have hw : Ample.LineBundles.sectionNonvanishing w = Ample.LineBundles.sectionNonvanishing s ⊓ Ample.LineBundles.sectionNonvanishing t := by
    exact (Ample.Powers.sectionNonvanishing_comp_iso _ (L.tensorPowerTensorIso M (b * a)).symm).trans
      ((Tensor.SectionNonvanishing.sectionNonvanishing_tensorProduct (L.tensorPower (b * a)) (M.tensorPower (b * a)) s' t').trans
        (congrArg₂ (fun U V : X.Opens => U ⊓ V) hs' ht'))
  exact ⟨b * a, Nat.mul_pos hb ha, w, hw.symm ▸ ⟨hxs, hxt⟩, hw.symm ▸ hs.inf ht⟩

theorem Line.Bundles.LineBundle.IsAmple.tensor_of_separated [X.IsSeparated]
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple :=
  hL.tensor hM

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
