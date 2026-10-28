import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSectionSurjectivity

/-! # Resolution Complex Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact

noncomputable section

/-!
# IntegralComparison: the short exact sequence of the original crystalline resolution complexes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := p) (J := J) (δ := δ) f
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f

def presheafComplex : CochainComplex ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u + 1} R) ℕ :=
  ((sheafToPresheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I).cocomplex

def sequence : ShortComplex (CochainComplex (ModuleCat.{u + 1} R) ℕ) :=
  BoundedSection.ComplexExact.sequence R P (BoundedSection.Reconstruction.monotone_property f)
    (ModuleCat.of R R) (presheafComplex f)

theorem shortExact : (sequence (p := p) (J := J) (δ := δ) f).ShortExact :=
  BoundedSection.ComplexExact.shortExact R P (BoundedSection.Reconstruction.monotone_property f)
    (ModuleCat.of R R) (presheafComplex f)
    (fun i n => ResolutionSectionSurjectivity.transition_surjective f i n (n + 1) (Nat.le_succ n))

def sourceIso :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (sequence (p := p) (J := J) (δ := δ) f).X₁ ≅
      BoundedResolution.Comparison.complex (p := p) (J := J) (δ := δ) f := Iso.refl _

def sourceHomologyIso (i : ℕ) :
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).obj
      ((sequence (p := p) (J := J) (δ := δ) f).X₁.homology i) ≅
        ModuleCat.of R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  (((sequence f).X₁.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{u + 2, u + 1} R)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (sourceIso f) ≪≫
      BoundedResolution.Comparison.homologyIso f i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact
