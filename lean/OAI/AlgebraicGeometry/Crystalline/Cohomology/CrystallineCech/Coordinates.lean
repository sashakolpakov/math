import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechFunctorCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinates.CrystallineCechCoordinates

noncomputable section

/-!
# The original crystalline Čech computation in intersection coordinates

Functoriality identifies the entire native section double complex,
including both differentials, with Čech cochains of the actual Zariski
image of the original injective resolution.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "J" => Opens.grothendieckTopology X.left

local instance coefficientLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

local instance moduleCoproducts : HasCoproducts.{0} V := fun T =>
  (LargeZariski.Colimits.LargeZariskiColimits.modules (Site.CoefficientRing p k)).has_colimits_of_shape (Discrete T)

local instance cech_additive : (cechComplexFunctor (A := V) U).Additive :=
  Functor.additive_of_iso (LargeZariski.CechFunctorCoordinates.LargeZariskiCechFunctorCoordinates.presheafIso
    (Site.CoefficientRing p k) X.left U)

variable (F : Sheaf (Site.topology p k X)
  (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F)

def bicomplex : HomologicalComplex₂ V (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((sheafToPresheaf J V ⋙ cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I)

def bicomplexIso : CrystallineZariski.CechSections.CrystallineZariskiCechSections.sectionBicomplex p k X U F I ≅ bicomplex p k X U F I :=
  (NatIso.mapHomologicalComplex
    (LargeZariski.CechFunctorCoordinates.LargeZariskiCechFunctorCoordinates.sheafIso (Site.CoefficientRing p k) X.left U)
    (ComplexShape.up ℕ)).app (CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I)

def totalIso : CrystallineZariski.CechSections.CrystallineZariskiCechSections.sectionTotal p k X U F I ≅
    (bicomplex p k X U F I).total (ComplexShape.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso p k X U F I) (ComplexShape.up ℕ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinates.CrystallineCechCoordinates
