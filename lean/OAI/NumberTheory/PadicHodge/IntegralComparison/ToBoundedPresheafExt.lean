import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.SectionCohomologyCoordinates

/-! # To Bounded Presheaf Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ToBoundedPresheafExt.Big

noncomputable section

/-! The actual restriction of original resolution sections computes the original big-to-bounded crystalline Ext map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.restriction (p := p) (J := J) (δ := δ) f n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnitIso (p := p) (J := J) (δ := δ) f n
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

theorem component (i : ℕ) : IntegralComparison.Ext.ExtPullbackComparison.component T R A (e).inv i
    (BigCrystallineCohomology.structureSheaf f) =
      ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact (Ext.comp_mk₀_id _).symm

def complexMap :
    Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
      BigCrystallineSite.Object.topology I.cocomplex ⟶
    Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) (In).cocomplex :=
  Sheaf.PresheafSectionRestriction.complexMap G R (BoundedCrystalline.Site.topology f n)
    BigCrystallineSite.Object.topology I.cocomplex

theorem ext_homology (i : ℕ) :
    HomologicalComplex.homologyMap (IntegralComparison.Ext.ExtPullbackComparison.complexMap T R A (e).inv I.cocomplex) i ≫
      (InjectiveSectionCohomology.homologyIso R
        (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom =
    (InjectiveSectionCohomology.homologyIso R A I i).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) :=
  (IntegralComparison.Ext.ExtPullbackComparison.homology T R A (e).inv I i).trans
    (congrArg (fun a => (InjectiveSectionCohomology.homologyIso R A I i).hom ≫ a)
      (component f n i))

private theorem complexes_compatibility :
    IntegralComparison.Ext.ExtPullbackComparison.complexMap T R A (e).inv I.cocomplex ≫
      (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (In).cocomplex).hom =
    (Sheaf.PresheafSectionComplex.complexIso R BigCrystallineSite.Object.topology
      I.cocomplex).hom ≫ complexMap f n I :=
  Sheaf.ExtRestrictionCoordinates.complexes.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology f n)
    BigCrystallineSite.Object.topology I.cocomplex

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (complexMap f n I) i ≫
    (Sheaf.PresheafSectionComplex.homologyIso R (BoundedCrystalline.Site.topology f n) In i).hom =
      (Sheaf.PresheafSectionComplex.homologyIso R BigCrystallineSite.Object.topology I i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) :=
  Sheaf.SectionCohomologyCoordinates.homology.{u + 1, u, u + 2} R (BoundedCrystalline.Site.topology f n)
    BigCrystallineSite.Object.topology In I
    (IntegralComparison.Ext.ExtPullbackComparison.complexMap T R A (e).inv I.cocomplex) (complexMap f n I) i
    (ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i))
    (complexes_compatibility f n I)
    (ext_homology f n I i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ToBoundedPresheafExt.Big
