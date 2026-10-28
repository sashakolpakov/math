import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison

/-! # Affine Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison.BigAffineCrystallineComparison

noncomputable section

/-! # Original big affine crystalline Ext and the original completed PD complex -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

def complexIso : BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r ≅
    Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase :=
  BigCrystalline.IntrinsicSections.BigCrystallineIntrinsicSections.iso p k B σ (fun i => r (MvPolynomial.X i)) ≪≫
    CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryComplexIso p k B σ r ≪≫
      Affine.Comparison.AffineCrystallineComparison.complexIso p k B σ r hr hbase

def homologyIso (n : ℕ) :
    (Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase).homology n ≅
      ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) bX n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexIso p k B σ r hr hbase).symm ≪≫
    BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison.BigAffineCrystallineComparison
