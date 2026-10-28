import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.EquivalentProperties
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

/-! # Chart Open Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage

noncomputable section

/-!
# IntegralComparison: actual crystalline chart sections equal the Zariski resolution sections on the chart image
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (g : X ⟶ Y) [IsOpenImmersion g] (n : ℕ)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.property (p := p) (J := J) (δ := δ) fY g n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n g.opensRange
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

theorem property_iff (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) : P T ↔ Q T := by
  rw [BoundedOpen.Support.property_iff_range_subset]
  change (∃ t, t ≫ g = T.obj.mapToX) ↔ Set.range T.obj.mapToX ⊆ Set.range g
  constructor
  · rintro ⟨t, ht⟩ x ⟨w, rfl⟩
    exact ⟨t w, congrArg (fun a => a w) ht⟩
  · intro h
    exact ⟨IsOpenImmersion.lift g T.obj.mapToX h, IsOpenImmersion.lift_fac g T.obj.mapToX h⟩

def linearEquiv (F : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :
    Incoming.SectionRestriction.Sections R (ModuleCat.of R R) P F.obj ≃ₗ[R] Incoming.SectionRestriction.Sections R (ModuleCat.of R R) Q F.obj :=
  Incoming.EquivalentProperties.linearEquiv R (ModuleCat.of R R) P Q
    (fun T h => (property_iff fY g n T).mp h) (fun T h => (property_iff fY g n T).mpr h) F.obj

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def complexIso : BoundedOpen.Resolution.complex fY g n I ≅
    BoundedOpen.Resolution.complex fY g.opensRange.ι n I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapIso (linearEquiv fY g n (I.cocomplex.X i)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def evaluationIso : BoundedOpen.Resolution.complex fY g n I ≅
    ((BoundedOpen.SectionComplex.evaluation (B := B) g.opensRange).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedOpen.SectionComplex.complex fY n I) :=
  complexIso fY g n I ≪≫ (BoundedOpen.SectionComplex.evaluationIso fY n I g.opensRange).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage
