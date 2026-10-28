import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeLifts

/-! # Frame Slice Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FrameSliceQuasiIso.OpenFrameSliceQuasiIso

noncomputable section

/-! An affine frame's original Poincaré augmentation transfers to the slice
over its actual globally postcomposed frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (IntegralComparison.BoundedFrame.Diagram.augmentation F)]

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram (CategoryTheory.Functor.obj G F)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection (CategoryTheory.Functor.obj G F)

theorem restricted : QuasiIso
    (((PresheafRestriction.PresheafRestrictionQuasiIso.restriction (V := ModuleCat.{u} B) G).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.Diagram.augmentation ((G).obj F))) := by
  have h : QuasiIso (IntegralComparison.BoundedFrame.OpenAugmentation.mappedAugmentation g hg n F) := by
    apply (quasiIso_iff_comp_right _ (IntegralComparison.BoundedFrame.OpenRestriction.presheafIso g hg n F).hom).mp
    rw [IntegralComparison.BoundedFrame.OpenAugmentation.augmentation]
    infer_instance
  have hr : QuasiIso (IntegralComparison.Relative.RestrictionAugmentation.mappedAugmentation G P QY π) :=
    (quasiIso_iff_comp_left (IntegralComparison.Relative.PostcomposeAugmentation.sourceIso g hg QX).inv _).mp h
  exact (quasiIso_iff_comp_left (IntegralComparison.Relative.RestrictionAugmentation.sourceIso G QY).inv _).mp hr

theorem onSlice : QuasiIso
    (((PresheafRestriction.PresheafRestrictionQuasiIso.restriction (V := ModuleCat.{u} B)
      (Over.forget ((G).obj F))).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.Diagram.augmentation ((G).obj F))) := by
  let := restricted g hg n F
  exact PresheafRestriction.PresheafRestrictionQuasiIso.onSlice G
    (IntegralComparison.Bounded.PostcomposeLifts.incomingLifts g hg n) F (IntegralComparison.BoundedFrame.Diagram.augmentation ((G).obj F))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FrameSliceQuasiIso.OpenFrameSliceQuasiIso
