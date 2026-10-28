import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechPresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechResolution

/-! # Cech Presheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechPresheafCoordinates

noncomputable section

/-! The original bounded crystalline Cech total has the actual lifted presheaf Cech coordinates. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance smallLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

local instance largeLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance largeProducts : HasProducts.{u} (ModuleCat.{u + 2} R) :=
  fun T => (largeLimits (B := B)).has_limits_of_shape (Discrete T)

local instance smallCoproducts : HasCoproducts.{0} (ModuleCat.{u + 1} R) :=
  fun T => (AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits.LargeZariskiColimits.modules R).has_colimits_of_shape (Discrete T)

local instance largeColimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

local instance largeCoproducts : HasCoproducts.{0} (ModuleCat.{u + 2} R) :=
  fun T => (largeColimits (B := B)).has_colimits_of_shape (Discrete T)

local instance liftLimits : PreservesLimitsOfSize.{u, u} (ModuleCat.uliftFunctor.{u + 2, u + 1} R) :=
  preservesLimitsOfSize_shrink.{u, u + 1, u, u + 1} _

def presheafComplex : CochainComplex (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 1} R) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} R)).mapHomologicalComplex (.up ℕ)).obj
    (CechResolution.imageComplex fY n I)

def liftIso : CechCoefficient.Total.mappedComplex (ModuleCat.uliftFunctor.{u + 2, u + 1} R)
    (presheafComplex fY n I) ≅ BoundedOpen.SectionComplex.complex fY n I :=
  Iso.refl _

variable {ι : Type u} [Finite ι] (U : ι → Y.Opens)

def totalIso : CechResolution.total fY n I U ≅
    (CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech
      (BoundedOpen.SectionComplex.complex fY n I)).total (.up ℕ) :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).mapIso
    (ZariskiCechPresheafCoordinates.totalIso R Y U (CechResolution.imageComplex fY n I)) ≪≫
      CechCoefficient.Total.totalIso (ModuleCat.uliftFunctor.{u + 2, u + 1} R)
        (FormalCoproduct.mk ι U).cech (presheafComplex fY n I) ≪≫
          HomologicalComplex₂.total.mapIso
            (((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapHomologicalComplex
              (.up ℕ)).mapIso (liftIso fY n I)) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechPresheafCoordinates
