import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction

/-! # Frame Constants -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameConstants

noncomputable section

/-! The geometric frame source comparison is the native constant-sheaf restriction isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

omit [Fact p.Prime] [IsSeparated f] [IsSeparated fY] in
theorem component (i : ℕ) : (FrameSheafSections.sourceIso g hg n F).hom.f i =
    (ConstantSection.SectionRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)
      ((BoundedFrame.DeRhamSections.frameComplex f n F).X i)).hom := by
  let P := (Relative.ComplexRestriction.restriction (B := B) G).obj
    ((RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj).X i)
  let a := ((NatIso.mapHomologicalComplex (BoundedFrame.SheafRestriction.sheafificationIso (p := p) (J := J) (δ := δ) g hg n)
    (.up ℕ)).app (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj)).hom.f i
  have h := congrArg (fun b => a ≫ b) ((Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n).map_id P)
  exact h.trans (Category.comp_id _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameConstants
