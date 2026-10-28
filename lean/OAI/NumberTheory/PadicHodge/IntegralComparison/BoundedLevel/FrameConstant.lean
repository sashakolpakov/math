import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction

/-! # Frame Constant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameConstant

noncomputable section

/-! The geometric frame source comparison is the native constant-sheaf restriction isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm

omit [Fact p.Prime] [IsSeparated f]  in
theorem component (i : ℕ) : (FrameSheafSections.sourceIso f n m hnm F).hom.f i =
    (ConstantSection.SectionRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)
      ((BoundedFrame.DeRhamSections.frameComplex f n F).X i)).hom := by
  let P := (Relative.ComplexRestriction.restriction (B := B) G).obj
    ((RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj).X i)
  let a := ((NatIso.mapHomologicalComplex (FrameSheaves.sheafificationIso (p := p) (J := J) (δ := δ) f n m hnm)
    (.up ℕ)).app (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj)).hom.f i
  have h := congrArg (fun b => a ≫ b) ((Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n).map_id P)
  exact h.trans (Category.comp_id _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameConstant
