import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Sheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction

noncomputable section

/-!
# IntegralComparison: exact geometric restriction identifies the actual bounded frame sheaf complexes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) fY n
local notation "restriction" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sheafificationIso : SY ⋙ restriction ≅ Relative.ComplexRestriction.restriction (B := B) G ⋙ SX :=
  NatIso.ofComponents (fun P =>
    ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)).symm.app
        ((Bounded.RelativeSheafComplex.coefficientPresheaves fY n).obj P))
    (by
      intro P Q β
      exact ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
        (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)).symm.hom.naturality
          ((Bounded.RelativeSheafComplex.coefficientPresheaves fY n).map β))

variable [Fact p.Prime] [IsSeparated f] [IsSeparated fY] [Mono g]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

def complexIso :
    ((restriction).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Bounded.RelativeSheafComplex.complex fY n ((G).obj F)) ≅
        Bounded.RelativeSheafComplex.complex f n F :=
  (NatIso.mapHomologicalComplex (sheafificationIso g hg n) (ComplexShape.up ℕ)).app
    (Diagram.complex ((G).obj F)) ≪≫
      ((SX).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (OpenRestriction.presheafIso g hg n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction
