import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Frame Sheaves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheaves

noncomputable section

/-!
# IntegralComparison: exact restriction between Witt levels identifies the actual bounded frame sheaf complexes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f m
local notation "restriction" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def sheafificationIso : SY ⋙ restriction ≅ Relative.ComplexRestriction.restriction (B := B) G ⋙ SX :=
  NatIso.ofComponents (fun P =>
    ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).symm.app
        ((Bounded.RelativeSheafComplex.coefficientPresheaves f m).obj P))
    (by
      intro P Q β
      exact ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
        (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).symm.hom.naturality
          ((Bounded.RelativeSheafComplex.coefficientPresheaves f m).map β))

variable [Fact p.Prime] [IsSeparated f]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

def complexIso :
    ((restriction).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Bounded.RelativeSheafComplex.complex f m ((G).obj F)) ≅
        Bounded.RelativeSheafComplex.complex f n F :=
  (NatIso.mapHomologicalComplex (sheafificationIso f n m hnm) (ComplexShape.up ℕ)).app
    (BoundedFrame.Diagram.complex ((G).obj F)) ≪≫
      ((SX).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (FrameRestriction.presheafIso f n m hnm F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheaves
