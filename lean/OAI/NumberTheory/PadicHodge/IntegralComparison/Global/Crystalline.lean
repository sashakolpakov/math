import OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedCrystallineExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalConstantSheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison

noncomputable section

/-!
# IntegralComparison: the actual big-to-small crystalline cohomology comparison

Restriction preserves injectives by the proved exact extension. Its
constant-source Hom maps are bijective by local presentation covers and compatibility
with sheafification. Dimension shifting then proves that the existing
linear comparison map is bijective in every degree for separated X.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover (inclusion)
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff)

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]

local notation "W" => WittVector p k
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

instance wittSeparated : IsSeparated f := by
  change IsSeparated (X.hom ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k)))
  infer_instance

lemma mapExt_bijective (n : ℕ) : Function.Bijective
    ((Crystalline.Map.Comparison.restriction (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f).mapExtAddHom
      (BigCrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f)
      (BigCrystallineCohomology.structureSheaf f) n) := by
  apply Ext.Criterion.Comparison.bijective_of_hom_bijective
  intro Y
  exact LocalConstantSheafRestriction.map_bijective (Crystalline.PresentationCover.inclusion p k X)
    Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := W)))
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := W)) (Crystalline.ExactRestriction.Coeff (B := W))) Y

lemma comparison_bijective (n : ℕ) : Function.Bijective
    (Crystalline.Map.Comparison.integralComparison
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f n) :=
  (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := W))
    (Crystalline.Map.Comparison.constantTransport f)
    (Crystalline.Map.Comparison.structureTransport f) n).bijective.comp
      (mapExt_bijective p k X n)

def integralEquiv (n : ℕ) :
    BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f n ≃ₗ[Crystalline.ExactRestriction.Coeff (B := W)]
      Witt.Crystalline.integralCohomology p k X n :=
  LinearEquiv.ofBijective (Crystalline.Map.Comparison.integralComparison f n)
    (comparison_bijective p k X n)

def integralEquivWitt (n : ℕ) :
    BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f n ≃ₗ[W]
      Witt.Crystalline.integralCohomology p k X n where
  toEquiv := (integralEquiv p k X n).toEquiv
  map_add' := (integralEquiv p k X n).map_add
  map_smul' b x := (integralEquiv p k X n).map_smul (ULift.up b : Crystalline.ExactRestriction.Coeff (B := W)) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison
