import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase

/-! # Resolution Projection Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionCoordinates

noncomputable section

/-! Cohomology of the actual compatible-section projections is the original bounded crystalline restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

private theorem transport {C : Type*} [Category C] [Abelian C]
    {A A' B B' : CochainComplex C ℕ} (e : A ≅ A') (d : B ≅ B')
    (s : A ⟶ B) (r : A' ⟶ B') (hc : s ≫ d.hom = e.hom ≫ r) (i : ℕ)
    {U V : C} (a : A.homology i ⟶ U) (b : B.homology i ⟶ V) (g : U ⟶ V)
    (he : HomologicalComplex.homologyMap s i ≫ b = a ≫ g) :
    HomologicalComplex.homologyMap r i ≫ (HomologicalComplex.homologyMap d.inv i ≫ b) =
      (HomologicalComplex.homologyMap e.inv i ≫ a) ≫ g := by
  let H := HomologicalComplex.homologyFunctor C (.up ℕ) i
  have h : H.map s ≫ H.map d.hom = H.map e.hom ≫ H.map r :=
    (H.map_comp s d.hom).symm.trans ((congrArg H.map hc).trans (H.map_comp e.hom r))
  exact CoordinateSquare.Comparison.conjugate (H.mapIso e) (H.mapIso d)
    (H.map s) (H.map r) a b g h he

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.sourceComplexIso f I
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.targetComplexIso f n I
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionBase.Coordinates.extComplexMap f n I

private theorem homology_expanded (i : ℕ) : HomologicalComplex.homologyMap (ResolutionProjectionBase.Coordinates.projection f n I) i ≫
    (HomologicalComplex.homologyMap (d).inv i ≫
      (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom) =
    (HomologicalComplex.homologyMap (e).inv i ≫
      (InjectiveSectionCohomology.homologyIso R (BigCrystallineCohomology.constantUnit f) I i).hom) ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) :=
  @transport (ModuleCat.{u + 2} R) inferInstance inferInstance
    (InjectiveSectionCohomology.complex R (BigCrystallineCohomology.constantUnit f) I)
    (ResolutionProjectionBase.Coordinates.complex f I)
    (InjectiveSectionCohomology.complex R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In)
    (ResolutionProjectionBase.Coordinates.levelComplex f n I) e d s (ResolutionProjectionBase.Coordinates.projection f n I) (ResolutionProjectionBase.Coordinates.square f n I) i
    (ModuleCat.of R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i))
    (ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i))
    (InjectiveSectionCohomology.homologyIso R (BigCrystallineCohomology.constantUnit f) I i).hom
    (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom
    (ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i))
    (ResolutionProjectionBase.Coordinates.ext_homology f n I i)

private theorem source_homologyIso (i : ℕ) : (ResolutionProjectionBase.Coordinates.homologyIso f I i).hom =
    HomologicalComplex.homologyMap (e).inv i ≫
      (InjectiveSectionCohomology.homologyIso R (BigCrystallineCohomology.constantUnit f) I i).hom := rfl

private theorem target_homologyIso (i : ℕ) :
    (Sheaf.PresheafSectionComplex.homologyIso R (BoundedCrystalline.Site.topology f n) In i).hom =
      HomologicalComplex.homologyMap (d).inv i ≫
        (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom := rfl

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (ResolutionProjectionBase.Coordinates.projection f n I) i ≫
    (Sheaf.PresheafSectionComplex.homologyIso R (BoundedCrystalline.Site.topology f n) In i).hom =
      (ResolutionProjectionBase.Coordinates.homologyIso f I i).hom ≫ ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) := by
  rw [target_homologyIso, source_homologyIso]
  exact homology_expanded f n I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionCoordinates
