import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolutionLevels

/-! # Bounded Product Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology

noncomputable section

/-!
# IntegralComparison: the product resolution complex has the product of actual bounded crystalline cohomology
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.presheafComplex (p := p) (J := J) (δ := δ) f
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

def family : CochainComplex (Discrete ℕ ⥤ ModuleCat.{u + 1} R) ℕ :=
  BoundedSection.Family.complex R P (ModuleCat.of R R) A

def component (n : ℕ) : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  CountableProductHomology.component R (family (p := p) (J := J) (δ := δ) f) n

def levelIso (n : ℕ) :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (component (p := p) (J := J) (δ := δ) f n) ≅
        BoundedResolutionLevels.complex (p := p) (J := J) (δ := δ) f n := Iso.refl _

def componentHomologyIso (n i : ℕ) :
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).obj ((component (p := p) (J := J) (δ := δ) f n).homology i) ≅
      ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  (((component f n).sc i).mapHomologyIso (ModuleCat.uliftFunctor.{u + 2, u + 1} R)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (levelIso f n) ≪≫
      BoundedResolutionLevels.homologyIso f n i

def componentLinearEquiv (n i : ℕ) : (component (p := p) (J := J) (δ := δ) f n).homology i ≃ₗ[R]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  ULift.moduleEquiv.symm.trans (componentHomologyIso f n i).toLinearEquiv

def productHomologyLinearEquiv (i : ℕ) : (S).X₂.homology i ≃ₗ[R]
    (∀ n, BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  (CountableProductHomology.homologyIso R (family f) i).toLinearEquiv.trans
    (LinearEquiv.piCongrRight (fun n => componentLinearEquiv f n i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology
