import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction

/-! # Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf.Comparison

noncomputable section

/-! The canonical frame comparison in the original presheaf-section coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n F)]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n F

def map : ConstantSection.ComplexMap.source.{u + 1, u + 2} R D ⟶
    Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) I.cocomplex :=
  ConstantSection.ComplexRestriction.sectionMap R (BoundedCrystalline.Site.topology f n) D I.cocomplex
    (DeRhamSections.sheafMap f n F ≫ Injective.Comparison.map f n F I)

theorem factorization_component (i : ℕ) : (Comparison.map f n F I).f i =
    (DeRhamSections.sectionsMap f n F).f i ≫
      (Ext.ModuleFunctor.functor R A 0).map ((Injective.Comparison.map f n F I).f i) ≫
        (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) I.cocomplex).hom.f i :=
  (congrArg (fun a => a ≫ (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) I.cocomplex).hom.f i)
    (ConstantSection.ComplexComposition.component.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) D
      (DeRhamSections.sheafMap f n F) (Injective.Comparison.map f n F I) i)).trans
        (Category.assoc _ _ _)

/-- The section comparison factored through the injective resolution. -/
def factorizedMap : ConstantSection.ComplexMap.source.{u + 1, u + 2} R D ⟶
    Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) I.cocomplex :=
  DeRhamSections.sectionsMap f n F ≫
    ((Ext.ModuleFunctor.functor R A 0).mapHomologicalComplex (.up ℕ)).map
      (Injective.Comparison.map f n F I) ≫
        (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) I.cocomplex).hom

private theorem factorizedMap_component (i : ℕ) : (factorizedMap f n F I).f i =
    (DeRhamSections.sectionsMap f n F).f i ≫
      (Ext.ModuleFunctor.functor R A 0).map ((Injective.Comparison.map f n F I).f i) ≫
        (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) I.cocomplex).hom.f i := rfl

private theorem map_eq_factorized : Comparison.map f n F I = factorizedMap f n F I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (factorization_component f n F I i).trans
    (factorizedMap_component f n F I i).symm

theorem factorization : Comparison.map f n F I = factorizedMap f n F I :=
  map_eq_factorized f n F I

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf.Comparison
