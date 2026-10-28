import OAI.NumberTheory.PadicHodge.IntegralComparison.ToBoundedPresheafExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSheafSectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Reconstruction

/-! # Resolution Projection Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates

noncomputable section

/-! Projections of compatible sections of any original injective resolution compute the original bounded crystalline restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ExhaustiveSheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
    BigCrystallineSite.Object.topology (BoundedCrystalline.Site.property f)
    (BoundedSection.Reconstruction.monotone_property f) I.cocomplex

def levelComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) (In).cocomplex

def projection : complex f I ⟶ levelComplex f n I where
  «f» i := ModuleCat.ofHom (X := (complex f I).X i) (Y := (levelComplex f n I).X i)
    { toFun := fun x => ULift.up (x.down.val n)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

def homologyIso (i : ℕ) : (complex f I).homology i ≅
    ModuleCat.of R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  ExhaustiveSheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2} R
    BigCrystallineSite.Object.topology (BoundedCrystalline.Site.property f) (BoundedSection.Reconstruction.monotone_property f)
    (BoundedCrystalline.Site.exists_level f) I i

def sourceComplexIso : InjectiveSectionCohomology.complex R
    (BigCrystallineCohomology.constantUnit f) I ≅ complex f I :=
  ExhaustiveSheafSectionComplex.complexIso R BigCrystallineSite.Object.topology
    (BoundedCrystalline.Site.property f) (BoundedSection.Reconstruction.monotone_property f) (BoundedCrystalline.Site.exists_level f) I.cocomplex

def targetComplexIso : InjectiveSectionCohomology.complex R
    (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In ≅ levelComplex f n I :=
  Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (In).cocomplex

def extComplexMap : InjectiveSectionCohomology.complex R
    (BigCrystallineCohomology.constantUnit f) I ⟶
      InjectiveSectionCohomology.complex R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In :=
  Ext.ExtPullbackComparison.complexMap (BoundedCrystalline.Site.restriction f n) R
    (BigCrystallineCohomology.constantUnit f) (BoundedCrystalline.CrystallineCohomology.constantUnitIso f n).inv I.cocomplex

local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.sourceComplexIso f I
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.targetComplexIso f n I
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.extComplexMap f n I

theorem coordinates :
    (Sheaf.PresheafSectionComplex.complexIso R BigCrystallineSite.Object.topology I.cocomplex).hom ≫
      ToBoundedPresheafExt.Big.complexMap f n I = (e).hom ≫ projection f n I := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem square : s ≫ (d).hom = (e).hom ≫ projection f n I :=
  (Sheaf.ExtRestrictionCoordinates.complexes.{u + 1, u, u + 2}
    (BoundedCrystalline.Site.inclusion f n) R (BoundedCrystalline.Site.topology f n)
    BigCrystallineSite.Object.topology I.cocomplex).trans (coordinates f n I)

theorem ext_homology (i : ℕ) : HomologicalComplex.homologyMap s i ≫
    (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom =
      (InjectiveSectionCohomology.homologyIso R (BigCrystallineCohomology.constantUnit f) I i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) :=
  ToBoundedPresheafExt.Big.ext_homology f n I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates
