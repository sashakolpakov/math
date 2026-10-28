import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormSquare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistCoordinateForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusCoordinateForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusFrameCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeFormSymbols
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusAdditiveCoordinates

/-! # Relative Coordinate Identification -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification

noncomputable section

/-! # Identify the original polynomial coordinate maps with the explicit relative-form operators -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e (DividedPowers.DPMorphism.isDPMorphism he) hb
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)

local notation "I₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.dividedPowers p k σ
local notation "IG" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal (R n) σ (I₀ n)
local notation "γG" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (I₀ n) (δ₀ n)

abbrev Form (n j : ℕ) :=
  PD.DeRham.PDDeRham.Form (R n) (G n)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal (R n) σ (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ n))
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ n)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n)) j

def coordinates (n j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ (G n) j →+ Form p k σ n j :=
  BigCrystalline.TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W B I γ bX a
    (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)) j

def ambient (n j : ℕ) : Form p k σ n j →+ Form p k σ n j :=
  BigCrystalline.FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates.ambient p (Fact.out : p.Prime) W B σ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism hb a j
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n)

def power (n j : ℕ) : Form p k σ n j →+ Form p k σ n j :=
  BigCrystalline.FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates.power p (Fact.out : p.Prime) W B σ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism hb a j
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)

omit [PerfectRing k p] in
theorem coordinates_apply (n j : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ (G n) j) :
    coordinates p k σ n j z = BigCrystalline.TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W B I γ bX a
      (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)) j z := rfl

omit [Fintype σ] [LinearOrder σ] in
theorem ambient_apply (n j : ℕ) (ω : Form p k σ n j) :
    ambient p k σ n j ω =
      (BigCrystalline.RelativeForms.BigCrystallineRelativeForms.map a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n).op).f j ω :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map_apply
    ((BigCrystalline.RelativeForms.BigCrystallineRelativeForms.map a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n).op).f j) ω

omit [Fintype σ] [LinearOrder σ] in
theorem power_apply (n j : ℕ) (ω : Form p k σ n j) :
    power p k σ n j ω = (BigCrystalline.PowerForms.BigCrystallinePowerForms.component a p
      (op ((tw).obj (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)))).f j ω :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map_apply ((BigCrystalline.PowerForms.BigCrystallinePowerForms.component a p
    (op ((tw).obj (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)))).f j) ω

omit [PerfectRing k p] in
theorem coordinates_eq (n j : ℕ) :
    coordinates p k σ n j = FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.coordinates p k σ n j := rfl

omit [Fintype σ] [LinearOrder σ] in
theorem ambient_eq (n j : ℕ) :
    ambient p k σ n j = FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.ambient p k σ n j := by
  apply PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.addHom_ext (R n) (G n) (IG n) (γG n) j
  intro b v
  have hact := BigCrystalline.RelativeFormSymbols.BigCrystallineRelativeFormSymbols.map_symbol a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n).op j b v
  have hexp := PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_symbol (R n) (R n) (G n) (G n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.frobenius p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_coefficient p k σ n)
    (IG n) (γG n) (IG n) (γG n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_isDPMorphism p k σ n) j b v
  exact hact.trans hexp.symm

omit [Fintype σ] [LinearOrder σ] in
theorem power_eq (n j : ℕ) :
    power p k σ n j = FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.power p k σ n j := by
  apply PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.addHom_ext (R n) (G n) (IG n) (γG n) j
  intro b v
  have hact := BigCrystalline.RelativeFormSymbols.BigCrystallineRelativeFormSymbols.power_symbol a p
    (op ((tw).obj (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))) j b v
  have htw := BigCrystalline.RelativeFormSymbols.BigCrystallineRelativeFormSymbols.power_twist a bF e (he).isDPMorphism hb p
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)
  have hchange := congrArg (fun F : G n →ₐ[R n] G n =>
    PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γG n) (F b) (F ∘ v)) htw
  have hexp := PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap_symbol W (R n) (G n) (IG n) (γG n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.power p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.power_isDPMorphism p k σ n) j b v
  exact hact.trans (hchange.trans hexp.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification
