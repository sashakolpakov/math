import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves

/-! # Crystalline Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback

noncomputable section

/-!
# IntegralComparison: geometric pullback on the original bounded crystalline Ext groups
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n
local notation "restriction" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def constantTransport : (restriction).obj (CrystallineCohomology.constantUnit fY n) ≅
    CrystallineCohomology.constantUnit f n :=
  ((F).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) JX JY).symm.app
    ((Functor.const (Site.Objects (p := p) (J := J) (δ := δ) fY n)ᵒᵖ).obj
      (ModuleCat.of R R))

def pullback (i : ℕ) : CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i →ₗ[R]
    CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (Etale.Frobenius.extIsoCongr R (constantTransport g hg n)
    (BoundedOpen.Sheaves.structureTransport g hg n) i).toLinearMap.comp
      ((restriction).mapExtLinearMap R (CrystallineCohomology.constantUnit fY n)
        (CrystallineCohomology.structureSheaf fY n) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback
