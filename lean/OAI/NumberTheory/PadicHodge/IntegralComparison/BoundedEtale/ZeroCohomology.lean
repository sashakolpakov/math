import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroAcyclicTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Zero Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCohomology.Comparison

noncomputable section

/-!
# IntegralComparison: the native étale zero-frame resolution computes original cohomology

The coefficient-linear comparison uses the original Ext groups of the
structure sheaf restricted to the prescribed Witt level. All acyclicity
and resolution hypotheses are discharged by the actual frame construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f 0 F
local notation "ι" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.augmentation f 0 F

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Acyclic.Resolution.Comparison.complex R A K

def homologyIso (i : ℕ) : (complex p k C).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0 i) := by
  let : QuasiIso ι := ZeroResolution.augmentation_quasiIso p k C σ
  cases i with
  | zero => exact Acyclic.ResolutionZero.Comparison.homologyIso R A K ι
  | succ i =>
    exact Acyclic.Resolution.Comparison.positiveHomologyIso R A K ι
      (fun a q => ZeroAcyclicTerms.positive_cohomology_zero p k C σ a q) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCohomology.Comparison
