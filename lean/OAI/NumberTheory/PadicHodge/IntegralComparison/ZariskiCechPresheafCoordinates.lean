import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechFunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Zariski Cech Presheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechPresheafCoordinates

noncomputable section

/-! The original Zariski sheaf Cech section total is the native presheaf Cech total. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → X.Opens)

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{u + 1} R) :=
  fun J => (AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits.LargeZariskiColimits.modules R).has_colimits_of_shape (Discrete J)

local instance presheaves_additive :
    (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).Additive where
  map_add := rfl

local instance cech_additive : (cechComplexFunctor (A := ModuleCat.{u + 1} R) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u + 1} R)
    (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def functorIso : AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U ⋙
    (ZariskiCechSections.sections R X).mapHomologicalComplex (.up ℕ) ≅
      sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⋙ cechComplexFunctor U :=
  Functor.isoWhiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U)
    (NatIso.mapHomologicalComplex
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)
        (isTerminalTop : IsTerminal (⊤ : X.Opens))).symm (.up ℕ)) ≪≫
    AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechFunctorCoordinates.LargeZariskiCechFunctorCoordinates.sheafIso R X U

variable (A : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) ℕ)

def bicomplexIso : ZariskiCechSections.bicomplex R X U A ≅
    CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech
      (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex (.up ℕ)).obj A) :=
  (NatIso.mapHomologicalComplex (functorIso R X U) (.up ℕ)).app A

def totalIso : ZariskiCechSections.total R X U A ≅
    (CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech
      (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex (.up ℕ)).obj A)).total
        (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X U A) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechPresheafCoordinates
