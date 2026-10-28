import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProjectivePeriodData
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.AutomorphyBundle
import OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeCosets

/-! # Polarization Factor -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.ThetaConstruction

/-! A holomorphic factor for ThetaConstruction's original polarization. The integer
alternating form and its basis are constructed from the marking. -/

open scoped _root_.Manifold ContDiff

namespace PolarizationFactor.Geometric
open OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

def polarizationFactor (hE : E.transpose = -E) :
    (ProjectivePeriodData.Geometric.projectivePeriodData T).AutomorphyFactor where
  value l z := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy (DefinitionsIntegral.Geometric.integralLatticeBasis T)
    (DefinitionsIntegral.Geometric.integralLatticeForm T) T.lattice.subtype T.riemannForm l z
  zero z := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_zero _ _ _ _ z
  add l m z := RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_add _ _ _ _
    (DefinitionsIntegral.Geometric.integralLatticeForm_isAlt T hE) T.hermitian (DefinitionsIntegral.Geometric.integralLatticeForm_riemann T) l m z
  continuous l := (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_differentiable (DefinitionsIntegral.Geometric.integralLatticeBasis T)
    (DefinitionsIntegral.Geometric.integralLatticeForm T) T.lattice.subtype T.riemannForm l).continuous

theorem polarizationFactor_contDiff (hE : E.transpose = -E)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) :
    ContDiff ℂ ∞ ((polarizationFactor T hE).value l) :=
  RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_contDiff (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
    T.lattice.subtype T.riemannForm l

def polarizationBundle (hE : E.transpose = -E) :
    VectorBundleCore ℂ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus ℂ
      (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus :=
  (polarizationFactor T hE).vectorBundleCore

instance polarizationBundle_isContMDiff (hE : E.transpose = -E) :
    (polarizationBundle T hE).IsContMDiff 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞ :=
  (polarizationFactor T hE).vectorBundleCore_isContMDiff (polarizationFactor_contDiff T hE)

theorem polarizationFactor_square (hE : E.transpose = -E)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice)
    (z : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    (polarizationFactor T hE).value l z ^ 2 =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy T.riemannForm l.val z :=
  RepresentationTheory.Theta.Geometric.PeriodPolarizationAutomorphy.polarizationAutomorphy_sq (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
    T.lattice.subtype T.riemannForm l z

theorem polarizationFactor_double_lattice (hE : E.transpose = -E)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice)
    (hl : l ∈ (ProjectivePeriodData.Geometric.projectivePeriodData T).doubleSubgroup)
    (z : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    (polarizationFactor T hE).value l z =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy
        ((ProjectivePeriodData.Geometric.projectivePeriodData T).halfHermitian T.riemannForm) l.val z := by
  obtain ⟨m, hm⟩ := hl
  have hm' : (2 : ℕ) • m = l := by
    change (2 : ℤ) • m = l at hm
    simpa only [two_smul] using hm
  rw [← hm']
  exact RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy.polarizationAutomorphy_double_lattice (DefinitionsIntegral.Geometric.integralLatticeBasis T)
    (DefinitionsIntegral.Geometric.integralLatticeForm T) T.lattice.subtype T.riemannForm m z

end PolarizationFactor.Geometric

/-- The original factor also has the natural object-method spelling.
Both names denote the same constructed automorphy factor. -/
abbrev DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g}
    (T : DefinitionsIntegral.MarkedPolarizedTorus g E) (hE : E.transpose = -E) :
    (ProjectivePeriodData.Geometric.projectivePeriodData T).AutomorphyFactor :=
  PolarizationFactor.Geometric.polarizationFactor T hE

end AlgebraicGeometry.Picard.ThetaConstruction

namespace AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor.Geometric

/-! The actual marked lattice as the domain of the original theta factor. -/

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix)

def latticeEmbedding : F.lattice →+ (ProjectivePeriodData.Geometric.projectivePeriodData F).space := F.lattice.subtype

def integralLatticeEquiv : F.lattice ≃ₗ[ℤ] (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice :=
  LinearEquiv.refl ℤ F.lattice

theorem latticeEmbedding_symm (l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) :
    (latticeEmbedding F) ((integralLatticeEquiv F).symm l) = l.val := rfl

theorem latticeEquiv_polarization (_hP : matrix.transpose = -matrix) (l m : F.lattice) :
    (F.riemannForm ((latticeEmbedding F) l) ((latticeEmbedding F) m)).im =
      (DefinitionsIntegral.Geometric.integralLatticeForm F l m : ℝ) := DefinitionsIntegral.Geometric.integralLatticeForm_riemann F l m

end AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor.Geometric

end

end OAI
