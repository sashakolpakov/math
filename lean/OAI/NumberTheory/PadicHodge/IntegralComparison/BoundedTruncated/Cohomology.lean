import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.AcyclicTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Cohomology.Comparison

noncomputable section

/-!
# IntegralComparison: the native smooth finite-level frame resolution computes original cohomology

The coefficient-linear comparison uses the original Ext groups of the
structure sheaf restricted to the prescribed Witt level. All acyclicity
and resolution hypotheses are discharged by the actual frame construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Source" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "ι" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n F

def complex : CochainComplex (ModuleCat.{2} R) ℕ :=
  Acyclic.Resolution.Comparison.complex R Source K

def homologyIso (i : ℕ) : (complex p k n A C ρ hρ hker hbase).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) := by
  let : QuasiIso ι := Resolution.augmentation_quasiIso p k n A C σ ρ hρ hker hbase
  cases i with
  | zero => exact Acyclic.ResolutionZero.Comparison.homologyIso R Source K ι
  | succ i =>
    exact Acyclic.Resolution.Comparison.positiveHomologyIso R Source K ι
      (fun a q => AcyclicTerms.positive_cohomology_zero p k n A C σ ρ hρ hker hbase a q) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Cohomology.Comparison
