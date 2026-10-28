import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.Affine
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FlatScalarExtension
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SheafExactness
import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.RingTheory.Flat.Localization

/-! # Rational Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison.AffineRationalCrystallineComparison

noncomputable section

/-!
# Rational affine crystalline cohomology from the original completed forms

Localization is flat even for the original large cohomology modules.
Applying it to the proved integral comparison computes rational
crystalline cohomology by scalar extension of the actual completed
PD de Rham complex over the Witt-vector fraction field.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "K₀" => FractionRing W

def coefficients : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} K₀ :=
  ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* W).symm.toRingHom ⋙
    Large.FlatScalarExtension.LargeFlatScalarExtension.functor W K₀

instance coefficients_additive : (coefficients p k).Additive := by
  unfold coefficients
  infer_instance

instance coefficients_finiteLimits : PreservesFiniteLimits (coefficients p k) := by
  let : Module.Flat W K₀ := IsLocalization.flat K₀ (nonZeroDivisors W)
  unfold coefficients
  exact comp_preservesFiniteLimits _ _

instance coefficients_finiteColimits : PreservesFiniteColimits (coefficients p k) := by
  let : Module.Flat W K₀ := IsLocalization.flat K₀ (nonZeroDivisors W)
  unfold coefficients
  exact comp_preservesFiniteColimits _ _

instance coefficients_preservesHomology : (coefficients p k).PreservesHomology :=
  Functor.preservesHomologyOfExact _

variable (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

def complex : CochainComplex (ModuleCat.{u + 2} K₀) ℕ :=
  ((coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Finite.Affine.FiniteAffineCrystalline.complex p k B)

def cohomologyModuleIso (n : ℕ) :
    (coefficients p k).obj (ModuleCat.of R (Site.integralCohomology p k X n)) ≅
      Site.rationalCohomology p k X n := Iso.refl _

def homologyIso (n : ℕ) : (complex p k B).homology n ≅ Site.rationalCohomology p k X n :=
  Cech.SheafExactness.CechSheafExactness.mapHomologyIso (coefficients p k) (Finite.Affine.FiniteAffineCrystalline.complex p k B) n ≪≫
    (coefficients p k).mapIso (Finite.Affine.FiniteAffineCrystalline.homologyIso p k B n) ≪≫
      cohomologyModuleIso p k B n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison.AffineRationalCrystallineComparison
