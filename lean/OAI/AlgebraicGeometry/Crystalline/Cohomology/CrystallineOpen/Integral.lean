import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Sheaves
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective

/-! # Integral -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Integral.CrystallineOpenCohomology

noncomputable section

/-!
# Native crystalline cohomology restriction and restricted resolutions

The cohomology map is induced by the proved exact open restriction and
the canonical identifications of the original coefficient and structure
sheaves. Actual injective resolutions restrict to injective resolutions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Restriction" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j
local notation "Coefficients" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

def integralPullback (n : ℕ) : Site.integralCohomology p k Y n →ₗ[Coefficients]
    Site.integralCohomology p k X n :=
  NumberTheory.PadicHodge.PeriodInvariants.ExtTransport.exactTransport Coefficients Restriction
    (Sheaves.CrystallineOpenSheaves.coefficientIso p k j) (Sheaves.CrystallineOpenSheaves.structureIso p k j) n

def resolution (I : InjectiveResolution (Site.structureSheaf p k Y)) :
    InjectiveResolution ((Restriction).obj (Site.structureSheaf p k Y)) :=
  ExactInjective.ExactInjectiveResolution.map Restriction I

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Integral.CrystallineOpenCohomology
