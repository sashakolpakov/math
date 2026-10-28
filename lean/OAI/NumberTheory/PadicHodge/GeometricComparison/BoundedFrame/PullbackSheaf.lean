import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.AugmentationTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafificationStructure
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PullbackAugmentation

/-! # Pullback Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf

noncomputable section

/-! Arbitrary geometric frame pullback induces a map of the original bounded
crystalline sheaf resolutions, with the original structure augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) fY n

def map : ((R).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY) ⟶
    IntegralComparison.Bounded.RelativeSheafComplex.complex f n FX :=
  ((NatIso.mapHomologicalComplex (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n)
    (.up ℕ)).app (IntegralComparison.BoundedFrame.Diagram.complex FY)).hom ≫
      ((SX).mapHomologicalComplex (.up ℕ)).map (PullbackComplex.BoundedFramePullbackComplex.map g hg n FX FY α)

theorem component (i : ℕ) : (BoundedFramePullbackSheaf.map g hg n FX FY α).f i =
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n).hom.app
      ((IntegralComparison.BoundedFrame.Diagram.complex FY).X i) ≫
        (SX).map ((PullbackComplex.BoundedFramePullbackComplex.map g hg n FX FY α).f i) := rfl

theorem augmentation_zero : (IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg n FY).f 0 ≫
    (BoundedFramePullbackSheaf.map g hg n FX FY α).f 0 = (IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n FX).f 0 := by
  have h := IntegralComparison.Sheaf.AugmentationTransport.augmentation
    (IntegralComparison.Relative.ComplexRestriction.restriction (B := B) G) SY SX R
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n)
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso fY n)
    (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg n)
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso f n)
    (IntegralComparison.Bounded.SheafificationStructure.square g hg n)
    ((IntegralComparison.BoundedFrame.Diagram.augmentation FY).f 0)
    ((PullbackComplex.BoundedFramePullbackComplex.map g hg n FX FY α).f 0)
    ((IntegralComparison.BoundedFrame.Diagram.augmentation FX).f 0)
    (PullbackComplex.BoundedFramePullbackComplex.augmentation_zero g hg n FX FY α)
  have h₀ := IntegralComparison.BoundedFrame.PullbackAugmentation.zero g hg n FY
  have h₁ := IntegralComparison.Bounded.SheafAugmentationZero.zero fY n FY
  have h₂ := component g hg n FX FY α 0
  have h₃ := IntegralComparison.Bounded.SheafAugmentationZero.zero f n FX
  exact (congrArg₂ (fun a b => a ≫ b)
    (h₀.trans (congrArg (fun a => (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg n).inv ≫ (R).map a) h₁))
      h₂).trans ((Category.assoc _ _ _).trans (h.trans h₃.symm))

theorem augmentation : IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg n FY ≫
    BoundedFramePullbackSheaf.map g hg n FX FY α = IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n FX := by
  apply (CochainComplex.fromSingle₀Equiv (IntegralComparison.Bounded.RelativeSheafComplex.complex f n FX)
    (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf f n)).injective
  apply Subtype.ext
  exact augmentation_zero g hg n FX FY α

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf
