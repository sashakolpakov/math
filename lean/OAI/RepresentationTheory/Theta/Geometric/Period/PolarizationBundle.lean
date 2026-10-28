import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.AutomorphyBundle
import OAI.RepresentationTheory.Theta.Geometric.PeriodPolarizationAutomorphy

/-! # Polarization Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual reference polarization defines a complex line bundle
on each constructed period torus. -/

open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.referenceLatticePeriodEmbedding_symm (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l : (D.canonicalPeriodData hg x).periodIntegerLattice) :
    D.referenceLatticePeriodEmbedding x ((D.periodLatticeEquiv hg x).symm l) = l.val :=
  congrArg (fun w : (D.canonicalPeriodData hg x).periodIntegerLattice => w.val)
    ((D.periodLatticeEquiv hg x).apply_symm_apply l)

def Data.ActiveHeckeThetaData.periodPolarizationFactor (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.canonicalPeriodData hg x).AutomorphyFactor where
  value l z := D.periodPolarizationAutomorphy hg x ((D.periodLatticeEquiv hg x).symm l) z
  zero z := by
    rw [map_zero]
    exact PolarizationAutomorphy.polarizationAutomorphy_zero _ _ _ _ z
  add l m z := by
    rw [map_add]
    have h := D.periodPolarizationAutomorphy_add hg x ((D.periodLatticeEquiv hg x).symm l)
      ((D.periodLatticeEquiv hg x).symm m) z
    rw [D.referenceLatticePeriodEmbedding_symm] at h
    exact h
  continuous l :=
    (PolarizationAutomorphy.polarizationAutomorphy_differentiable (D.referenceBasis hg) D.pel.reference.integralForm
      (D.referenceLatticePeriodEmbedding x) (D.periodHermitian hg x)
      ((D.periodLatticeEquiv hg x).symm l)).continuous

def Data.ActiveHeckeThetaData.periodPolarizationBundle (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    VectorBundleCore ℂ (D.canonicalPeriodData hg x).periodTorus ℂ (D.canonicalPeriodData hg x).periodTorus :=
  (D.periodPolarizationFactor hg x).vectorBundleCore

instance Data.ActiveHeckeThetaData.periodPolarizationBundle_isContMDiff (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.periodPolarizationBundle hg x).IsContMDiff 𝓘(ℂ, (D.canonicalPeriodData hg x).space) ∞ := by
  apply (D.periodPolarizationFactor hg x).vectorBundleCore_isContMDiff
  intro l
  exact PolarizationAutomorphy.polarizationAutomorphy_contDiff (D.referenceBasis hg) D.pel.reference.integralForm
    (D.referenceLatticePeriodEmbedding x) (D.periodHermitian hg x)
    ((D.periodLatticeEquiv hg x).symm l)

end

end OAI.RepresentationTheory.Theta.Geometric
