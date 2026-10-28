import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

/-! # Pullback Constants -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackConstants

noncomputable section

/-! Geometric pullback and restriction to the original bounded site have the same constant-source identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n
local notation "BX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
local notation "BY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := fY)
local notation "Gn" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "IY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "Rn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "RX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.restriction (p := p) (J := J) (δ := δ) f n

theorem square :
    (Rn).mapIso (CrystallineCohomology.constantUnitIso fY n) ≪≫
      CrystallinePullback.constantTransport g hg n =
    (RX).mapIso (BigCrystallineCohomology.constantTransport g hg) ≪≫
      CrystallineCohomology.constantUnitIso f n := by
  have hL := PeriodInvariants.ConstantRestrictionCoherence.transport_comp JX JY BY Gn IY (ModuleCat.of R R)
  have hR := PeriodInvariants.ConstantRestrictionCoherence.transport_comp JX BX BY IX G (ModuleCat.of R R)
  exact hL.trans hR.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackConstants
