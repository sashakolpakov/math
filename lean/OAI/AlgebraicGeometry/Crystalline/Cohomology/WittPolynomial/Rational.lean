import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedWitt
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison

/-! # Rational -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Rational.WittPolynomialRationalCrystalline

noncomputable section

/-! # Original rational crystalline cohomology from the completed polynomial model -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "B" => MvPolynomial σ k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius.PolynomialFrobenius.ordinaryComplex p k σ
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex.WittPolynomialComplex.largeComplex p k σ

abbrev largeComplex : CochainComplex (ModuleCat.{u + 2} K₀) ℕ :=
  ((F).mapHomologicalComplex (.up ℕ)).obj L

def largeHomologyIso (n : ℕ) : (largeComplex p k σ).homology n ≅
    Site.rationalCohomology p k X n :=
  Cech.SheafExactness.CechSheafExactness.mapHomologyIso F L n ≪≫
    (F).mapIso (PolynomialComplex.WittPolynomialComplex.homologyIso p k σ n)

abbrev lift : ModuleCat.{u} K₀ ⥤ ModuleCat.{u + 2} K₀ := ModuleCat.uliftFunctor.{u + 2} K₀

instance lift_preservesHomology : (lift p k).PreservesHomology :=
  Functor.preservesHomologyOfExact _

def scalarLiftIso : largeComplex p k σ ≅
    (((lift p k).mapHomologicalComplex (.up ℕ)).obj C) :=
  (NatIso.mapHomologicalComplex (LiftedWitt.LiftedWittScalarExtension.iso p k K₀) (.up ℕ)).app
    (PolynomialComplex.WittPolynomialComplex.ordinaryComplex p k σ)

def liftedHomologyIso (n : ℕ) : (lift p k).obj ((C).homology n) ≅
    Site.rationalCohomology p k X n :=
  (Cech.SheafExactness.CechSheafExactness.mapHomologyIso (lift p k) C n).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (scalarLiftIso p k σ).symm ≪≫
      largeHomologyIso p k σ n

def homologyEquiv (n : ℕ) : (C).homology n ≃ₗ[K₀] Site.rationalCohomology p k X n :=
  ULift.moduleEquiv.symm.trans (liftedHomologyIso p k σ n).toLinearEquiv

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Rational.WittPolynomialRationalCrystalline
