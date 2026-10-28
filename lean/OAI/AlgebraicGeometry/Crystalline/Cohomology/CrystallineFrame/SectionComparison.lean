import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.GlobalAcyclic
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Section Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison

noncomputable section

/-!
# The actual finite frame resolution computes original affine crystalline Ext

All positive Ext groups of its terms vanish by the proved framed-tower
argument. The coefficient-linear acyclic-resolution comparison therefore
identifies the cohomology of its degree-zero Ext section complex with
the original integral crystalline cohomology in every degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.coefficientSheaf p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ (fun i => r (MvPolynomial.X i))
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.augmentation p k B σ (fun i => r (MvPolynomial.X i))

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A K

def homologyIso (n : ℕ) : (complex p k B σ r).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k X n) := by
  cases n with
  | zero => exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R A K ι
  | succ n =>
    exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R A K ι
      (fun j q => ⟨fun α β => (GlobalAcyclic.CrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q α).trans
        (GlobalAcyclic.CrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q β).symm⟩) n

def ordinaryComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R J K

def ordinaryComplexIso : complex p k B σ r ≅ ordinaryComplex p k B σ r :=
  NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J K

def ordinaryHomologyIso (n : ℕ) : (ordinaryComplex p k B σ r).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k X n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (ordinaryComplexIso p k B σ r).symm ≪≫
    homologyIso p k B σ r hr hbase n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison
