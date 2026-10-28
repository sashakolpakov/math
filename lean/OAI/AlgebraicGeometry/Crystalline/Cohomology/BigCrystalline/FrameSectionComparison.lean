import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Frame Section Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison

noncomputable section

/-! # Original big crystalline Ext is computed by the actual polynomial frame resolution -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX (fun i => r (MvPolynomial.X i))
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ bX (fun i => r (MvPolynomial.X i))

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A K

def homologyIso (n : ℕ) : (complex p k B σ r).homology n ≅
    ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) bX n) := by
  cases n with
  | zero => exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R A K α
  | succ n =>
    exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R A K α
      (fun j q => ⟨fun x y => (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q x).trans
        (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q y).symm⟩) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison
