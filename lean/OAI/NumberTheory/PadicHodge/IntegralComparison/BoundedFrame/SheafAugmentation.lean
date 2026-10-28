import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.AugmentationTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafificationStructure
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PullbackAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenAugmentationZero

/-! # Sheaf Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation

noncomputable section

/-!
# IntegralComparison: geometric restriction preserves the original bounded frame sheaf augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) fY n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

theorem comparison_f (i : ℕ) : (SheafRestriction.complexIso g hg n F).hom.f i =
    (SheafRestriction.sheafificationIso g hg n).hom.app
      ((Diagram.complex ((G).obj F)).X i) ≫
        (SX).map ((OpenRestriction.presheafIso g hg n F).hom.f i) := rfl

theorem zero : (PullbackAugmentation.augmentation g hg n ((G).obj F)).f 0 ≫
    (SheafRestriction.complexIso g hg n F).hom.f 0 =
      (Bounded.RelativeSheafComplex.augmentation f n F).f 0 := by
  have h := Sheaf.AugmentationTransport.augmentation
    (Relative.ComplexRestriction.restriction (B := B) G) SY SX R
    (SheafRestriction.sheafificationIso g hg n)
    (Bounded.RelativeSheafComplex.structureIso fY n)
    (BoundedOpen.Sheaves.structureTransport g hg n)
    (Bounded.RelativeSheafComplex.structureIso f n)
    (Bounded.SheafificationStructure.square g hg n)
    (RelativeCrystalline.ModuleComplex.augmentationZero
      (Diagram.productDiagram ((G).obj F)) QY
      (Diagram.projection ((G).obj F)))
    ((OpenRestriction.presheafIso g hg n F).hom.f 0)
    (RelativeCrystalline.ModuleComplex.augmentationZero
      (Diagram.productDiagram F) QX (Diagram.projection F))
    (OpenAugmentationZero.zero g hg n F)
  have h₀ := PullbackAugmentation.zero g hg n ((G).obj F)
  have h₁ := Bounded.SheafAugmentationZero.zero fY n ((G).obj F)
  have h₂ := comparison_f g hg n F 0
  have h₃ := Bounded.SheafAugmentationZero.zero f n F
  exact (congrArg₂ (fun a b => a ≫ b)
    (h₀.trans (congrArg (fun a => (BoundedOpen.Sheaves.structureTransport g hg n).inv ≫ (R).map a) h₁))
      h₂).trans ((Category.assoc _ _ _).trans (h.trans h₃.symm))

theorem augmentation : PullbackAugmentation.augmentation g hg n ((G).obj F) ≫
    (SheafRestriction.complexIso g hg n F).hom =
      Bounded.RelativeSheafComplex.augmentation f n F := by
  apply (CochainComplex.fromSingle₀Equiv (Bounded.RelativeSheafComplex.complex f n F)
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)).injective
  apply Subtype.ext
  exact zero g hg n F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation
