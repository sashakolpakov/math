import OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCechIntersections

/-! # Proper Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCech.CrystallineProperCechCohomology

noncomputable section

/-! # Unconditional global Čech computation on the actual proper affine cover -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]

def integralComplex : CochainComplex (ModuleCat.{u + 2} (Site.CoefficientRing p k)) ℕ :=
  GlobalCech.CrystallineGlobalCechCohomology.integralComplex p k X (ProperCechIntersections.CrystallineProperCechIntersections.opens k X)
    (injectiveResolution (Site.structureSheaf p k X))

def integralHomologyIso (n : ℕ) : (integralComplex p k X).homology n ≅
    ModuleCat.of (Site.CoefficientRing p k) (Site.integralCohomology p k X n) :=
  GlobalCech.CrystallineGlobalCechCohomology.integralHomologyIso p k X (ProperCechIntersections.CrystallineProperCechIntersections.opens k X)
    (injectiveResolution (Site.structureSheaf p k X))
    (ProperCechIntersections.CrystallineProperCechIntersections.covering k X) n

variable [PerfectRing k p]

def rationalComplex : CochainComplex (ModuleCat.{u + 2} (FractionRing (WittVector p k))) ℕ :=
  GlobalCech.CrystallineGlobalCechCohomology.rationalComplex p k X (ProperCechIntersections.CrystallineProperCechIntersections.opens k X)
    (injectiveResolution (Site.structureSheaf p k X))

def rationalHomologyIso (n : ℕ) : (rationalComplex p k X).homology n ≅
    Site.rationalCohomology p k X n :=
  GlobalCech.CrystallineGlobalCechCohomology.rationalHomologyIso p k X (ProperCechIntersections.CrystallineProperCechIntersections.opens k X)
    (injectiveResolution (Site.structureSheaf p k X))
    (ProperCechIntersections.CrystallineProperCechIntersections.covering k X) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCech.CrystallineProperCechCohomology
