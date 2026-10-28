import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackConstants
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.LinearTransportComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Pullback Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackRestriction

noncomputable section

/-! The actual big crystalline pullback commutes with restriction to every original bounded crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) g hg
local notation "Gn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "RX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.restriction (p := p) (J := J) (δ := δ) f n
local notation "RY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.restriction (p := p) (J := J) (δ := δ) fY n
local notation "BY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY

theorem structure_square :
    (Gn).mapIso (Iso.refl ((RY).obj BY)) ≪≫ BoundedOpen.Sheaves.structureTransport g hg n =
      (RX).mapIso (BigCrystallineCohomology.structureTransport g hg) ≪≫ Iso.refl _ := by
  rw [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]
  exact Iso.refl_trans _

theorem naturality (i : ℕ)
    (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY i) :
    CrystallinePullback.pullback g hg n i (CrystallineCohomology.restriction fY n i x) =
      CrystallineCohomology.restriction f n i (BigCrystallineCohomology.pullback g hg i x) := by
  have hL := Ext.LinearTransportComposition.composition R RY Gn
    (CrystallineCohomology.constantUnitIso fY n) (Iso.refl _)
    (CrystallinePullback.constantTransport g hg n) (BoundedOpen.Sheaves.structureTransport g hg n) x
  have hR := Ext.LinearTransportComposition.composition R G RX
    (BigCrystallineCohomology.constantTransport g hg) (BigCrystallineCohomology.structureTransport g hg)
    (CrystallineCohomology.constantUnitIso f n) (Iso.refl _) x
  have hm := congrArg₂ (fun eA eB => Ext.LinearTransportComposition.map R ((RY) ⋙ (Gn)) eA eB i x)
    (PullbackConstants.square g hg n) (structure_square g hg n)
  exact hL.trans (hm.trans hR.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackRestriction
