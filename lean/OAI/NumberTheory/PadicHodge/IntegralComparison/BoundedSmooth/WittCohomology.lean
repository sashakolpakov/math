import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Witt Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCohomology.Comparison

noncomputable section

/-!
# IntegralComparison: the native smooth Witt frame resolution computes original cohomology

The coefficient-linear comparison uses the original Ext groups of the
structure sheaf restricted to the prescribed Witt level. All acyclicity
and resolution hypotheses are discharged by the actual frame construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Source" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "ι" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n F

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Acyclic.Resolution.Comparison.complex R Source K

def homologyIso (i : ℕ) : (complex p k A C ρ hρ hker hbase n).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) := by
  let : QuasiIso ι := WittResolution.augmentation_quasiIso p k A C σ ρ hρ hker hbase n
  cases i with
  | zero => exact Acyclic.ResolutionZero.Comparison.homologyIso R Source K ι
  | succ i =>
    exact Acyclic.Resolution.Comparison.positiveHomologyIso R Source K ι
      (fun a q => WittAcyclicTerms.positive_cohomology_zero p k A C σ ρ hρ hker hbase n a q) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCohomology.Comparison
