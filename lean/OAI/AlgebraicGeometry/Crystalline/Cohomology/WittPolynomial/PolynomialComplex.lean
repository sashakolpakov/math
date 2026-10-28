import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameCompletion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorEquivalence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison

/-! # Polynomial Complex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex.WittPolynomialComplex

noncomputable section

/-!
# The actual polynomial crystalline complex is the integral completion of ordinary forms

The coefficient equivalence intertwines the original partial derivatives.
Finite exterior powers then identify the completed ordinary complex with
the actual inverse system of divided-power forms, before rationalization.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
abbrev derivative (i : σ) : Module.End W P := (MvPolynomial.pderiv i).toLinearMap

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex.WittPolynomialComplex.derivative p k σ
local notation "hD" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomial_derivatives_commute W σ
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.derivative p k B σ r hr hb
local notation "hL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.commute p k B σ r hr hb

abbrev completion : ModuleCat.{u} W ⥤ ModuleCat.{u} W :=
  NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear.functor I

abbrev ordinaryComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  ((completion p k).mapHomologicalComplex (.up ℕ)).obj (DeRhamPresentationTo.DeRhamPresentation.complex W P)

def coefficientComplexIso : NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion.target I D hD ≅
    Affine.PolynomialOperators.AffinePolynomialOperators.complex p k B σ r hr hb :=
  Koszul.TensorEquivalence.KoszulTensorEquivalence.complexIso W σ (AdicCompletion I P) C
    (NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion.operator I D) L
    (NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion.commute I D hD) hL
    (FrameCompletion.WittPolynomialFrameCompletion.completedEquiv p k σ)
    (FrameCompletion.WittPolynomialFrameCompletion.completed_derivative p k σ)

def coordinateComplexIso :
    ((completion p k).mapHomologicalComplex (.up ℕ)).obj
      (Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ) ≅
        Affine.PolynomialOperators.AffinePolynomialOperators.complex p k B σ r hr hb :=
  NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion.complexIso I (Submodule.fg_span_singleton _) D hD ≪≫
    coefficientComplexIso p k σ

def tensorComplexIso : ordinaryComplex p k σ ≅
    Affine.PolynomialOperators.AffinePolynomialOperators.complex p k B σ r hr hb :=
  ((completion p k).mapHomologicalComplex (.up ℕ)).mapIso
      (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).symm ≪≫
    coordinateComplexIso p k σ

def complexIso : ordinaryComplex p k σ ≅ PD.PDDeRham.complex p k B Tower :=
  tensorComplexIso p k σ ≪≫ Affine.PolynomialComparison.AffinePolynomialComparison.complexIso p k B σ r hr hb

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "Lift" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
local notation "Large" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison.largeLift p k

abbrev largeComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((Large).mapHomologicalComplex (.up ℕ)).obj
    (((Lift).mapHomologicalComplex (.up ℕ)).obj (ordinaryComplex p k σ))

def largeComplexIso : largeComplex p k σ ≅
    Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hb :=
  ((Large).mapHomologicalComplex (.up ℕ)).mapIso
    (((Lift).mapHomologicalComplex (.up ℕ)).mapIso (complexIso p k σ))

def homologyIso (n : ℕ) : (largeComplex p k σ).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k
      (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (largeComplexIso p k σ) ≪≫
    Affine.Comparison.AffineCrystallineComparison.homologyIso p k B σ r hr hb n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex.WittPolynomialComplex
