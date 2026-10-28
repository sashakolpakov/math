import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.CoefficientComparison.BigCrystallineCoefficientComparison

noncomputable section

/-! # Big-to-small crystalline Ext comparison with arbitrary coefficients

The fixed-source comparison applies to every sheaf of coefficient modules.
In particular, acyclicity of a restricted resolution term detects its
acyclicity on the original big crystalline site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover (inclusion)
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff ModuleSheaf)

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]

local notation "W" => WittVector p k
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map.Comparison.restriction (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f

theorem mapExt_bijective (Y : NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f) (n : ℕ) :
    Function.Bijective ((F).mapExtAddHom A Y n) := by
  apply NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion.Comparison.bijective_of_hom_bijective
  intro Z
  exact NumberTheory.PadicHodge.IntegralComparison.LocalConstantSheafRestriction.map_bijective (NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover.inclusion p k X)
    NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site.AffineThickening.topology NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)))
    (ModuleCat.of (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)) (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))) Z

def equivalence (Y : NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f) (n : ℕ) :
    Ext.{u + 2} A Y n ≃ₗ[NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)] Ext.{u + 2} ((F).obj A) ((F).obj Y) n :=
  LinearEquiv.ofBijective ((F).mapExtLinearMap (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)) A Y n)
    (mapExt_bijective p k X Y n)

theorem subsingleton_iff (Y : NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f) (n : ℕ) :
    Subsingleton (Ext.{u + 2} A Y n) ↔ Subsingleton (Ext.{u + 2} ((F).obj A) ((F).obj Y) n) := by
  constructor
  · intro h
    exact ⟨fun x y => by
      obtain ⟨a, rfl⟩ := (mapExt_bijective p k X Y n).surjective x
      obtain ⟨b, rfl⟩ := (mapExt_bijective p k X Y n).surjective y
      exact congrArg ((F).mapExtAddHom A Y n) (h.elim a b)⟩
  · intro h
    exact ⟨fun a b => (mapExt_bijective p k X Y n).injective (h.elim _ _)⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.CoefficientComparison.BigCrystallineCoefficientComparison
