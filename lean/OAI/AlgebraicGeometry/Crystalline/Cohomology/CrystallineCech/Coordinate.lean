import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinates

/-! # Coordinate -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinate.CrystallineCechCoordinateCohomology

noncomputable section

/-! # Original crystalline cohomology from the actual intersection double complex -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)
  (I : InjectiveResolution (Site.structureSheaf p k X))

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{u + 1} (Site.CoefficientRing p k)) :=
  fun T => (LargeZariski.Colimits.LargeZariskiColimits.modules (Site.CoefficientRing p k)).has_colimits_of_shape (Discrete T)

def integralComplex : CochainComplex (ModuleCat.{u + 2} (Site.CoefficientRing p k)) ℕ :=
  ((GlobalCech.CrystallineGlobalCechCohomology.liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((Coordinates.CrystallineCechCoordinates.bicomplex p k X U (Site.structureSheaf p k X) I).total
      (ComplexShape.up ℕ))

def integralComplexIso : GlobalCech.CrystallineGlobalCechCohomology.integralComplex p k X U I ≅
    integralComplex p k X U I :=
  ((GlobalCech.CrystallineGlobalCechCohomology.liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (Coordinates.CrystallineCechCoordinates.totalIso p k X U (Site.structureSheaf p k X) I)

def integralHomologyIso (hU : iSup U = ⊤) (n : ℕ) : (integralComplex p k X U I).homology n ≅
    ModuleCat.of (Site.CoefficientRing p k) (Site.integralCohomology p k X n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (integralComplexIso p k X U I).symm ≪≫
    GlobalCech.CrystallineGlobalCechCohomology.integralHomologyIso p k X U I hU n

variable [PerfectRing k p]

def rationalComplex : CochainComplex (ModuleCat.{u + 2} (FractionRing (WittVector p k))) ℕ :=
  ((Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (integralComplex p k X U I)

def rationalHomologyIso (hU : iSup U = ⊤) (n : ℕ) : (rationalComplex p k X U I).homology n ≅
    Site.rationalCohomology p k X n :=
  Cech.SheafExactness.CechSheafExactness.mapHomologyIso (Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k)
    (integralComplex p k X U I) n ≪≫
      (Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k).mapIso
        (integralHomologyIso p k X U I hU n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinate.CrystallineCechCoordinateCohomology
