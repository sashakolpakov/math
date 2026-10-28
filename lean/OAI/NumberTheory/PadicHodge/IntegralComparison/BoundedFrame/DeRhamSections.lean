import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # De Rham Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections

noncomputable section

/-!
# IntegralComparison: the actual frame de Rham complex maps into bounded crystalline sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F

instance coefficientFunctor_additive : (Crystalline.RelativeResolution.coefficientFunctor (B := B)).Additive where
  map_add := by intros; rfl

def frameComplex : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  ((Crystalline.RelativeResolution.coefficientFunctor (B := B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (RelativeFrame.ComplexMap.frameComplex F.obj)

def sheafMap :
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (frameComplex f n F) ⟶ K :=
  ((S).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeFrame.ComplexMap.map H Q π F.obj τ)

def sectionsMap :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (frameComplex f n F) ⟶
    Acyclic.Resolution.Comparison.complex R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) K :=
  ConstantSection.ComplexMap.map R (BoundedCrystalline.Site.topology f n) (frameComplex f n F) K (sheafMap f n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
