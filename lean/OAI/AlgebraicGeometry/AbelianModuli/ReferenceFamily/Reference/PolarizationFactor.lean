import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.RepresentationTheory.Theta.Geometric.AutomorphyBundleMetric
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.AutomorphyBundle
import OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeCosets

/-! # Polarization Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The original integral form defines a holomorphic polarization
factor on the actual reference torus. Its semicharacter uses the one
fixed reference basis, with no doubling of the original polarization. -/

open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

def Fiber.ReferenceAnalyticFiber.latticeEmbedding : P.lattice →+ Fiber.ReferenceTangent s :=
  F.periodEmbedding.comp P.lattice.subtype.toAddMonoidHom

theorem Fiber.ReferenceAnalyticFiber.latticeEmbedding_symm (l : F.periodData.periodIntegerLattice) :
    F.latticeEmbedding (F.integralLatticeEquiv.symm l) = l.val :=
  congrArg (fun w : F.periodData.periodIntegerLattice => w.val)
    (F.integralLatticeEquiv.apply_symm_apply l)

include hP in
theorem Fiber.ReferenceAnalyticFiber.referenceForm_isAlt : P.integralForm.IsAlt := by
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, ha, _⟩
  exact ha

def Fiber.ReferenceAnalyticFiber.polarizationAutomorphy : P.lattice → Fiber.ReferenceTangent s → ℂ :=
  RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form

theorem Fiber.ReferenceAnalyticFiber.polarizationAutomorphy_add (l m : P.lattice) (w : Fiber.ReferenceTangent s) :
    F.polarizationAutomorphy hP (l + m) w =
      F.polarizationAutomorphy hP l (w + F.latticeEmbedding m) * F.polarizationAutomorphy hP m w :=
  RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_add _ _ _ _ (Fiber.ReferenceAnalyticFiber.referenceForm_isAlt hP)
    F.hermitian (F.latticeEquiv_polarization hP) l m w

def Fiber.ReferenceAnalyticFiber.polarizationFactor : F.periodData.AutomorphyFactor where
  value l w := F.polarizationAutomorphy hP (F.integralLatticeEquiv.symm l) w
  zero w := by
    rw [map_zero]
    exact RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_zero _ _ _ _ w
  add l m w := by
    rw [map_add]
    have h := F.polarizationAutomorphy_add hP (F.integralLatticeEquiv.symm l)
      (F.integralLatticeEquiv.symm m) w
    rw [F.latticeEmbedding_symm] at h
    exact h
  continuous l :=
    (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_differentiable (P.referenceBasis hP) P.integralForm
      F.latticeEmbedding F.form (F.integralLatticeEquiv.symm l)).continuous

theorem Fiber.ReferenceAnalyticFiber.polarizationFactor_contDiff (l : F.periodData.periodIntegerLattice) :
    ContDiff ℂ ∞ ((F.polarizationFactor hP).value l) :=
  RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_contDiff (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form
    (F.integralLatticeEquiv.symm l)

def Fiber.ReferenceAnalyticFiber.polarizationBundle : VectorBundleCore ℂ F.periodData.periodTorus ℂ F.periodData.periodTorus :=
  (F.polarizationFactor hP).vectorBundleCore

instance Fiber.ReferenceAnalyticFiber.polarizationBundle_isContMDiff : (F.polarizationBundle hP).IsContMDiff
    𝓘(ℂ, F.periodData.space) ∞ :=
  (F.polarizationFactor hP).vectorBundleCore_isContMDiff (F.polarizationFactor_contDiff hP)

theorem Fiber.ReferenceAnalyticFiber.polarizationFactor_square (l : F.periodData.periodIntegerLattice) (w : F.periodData.space) :
    (F.polarizationFactor hP).value l w ^ 2 = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy F.form l.val w := by
  have h := RepresentationTheory.Theta.Geometric.PeriodPolarizationAutomorphy.polarizationAutomorphy_sq (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form
    (F.integralLatticeEquiv.symm l) w
  rw [F.latticeEmbedding_symm] at h
  exact h

theorem Fiber.ReferenceAnalyticFiber.polarizationFactor_double_lattice (l : F.periodData.periodIntegerLattice)
    (hl : l ∈ F.periodData.doubleSubgroup) (w : F.periodData.space) :
    (F.polarizationFactor hP).value l w =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (F.periodData.halfHermitian F.form) l.val w := by
  obtain ⟨m, hm⟩ := hl
  have hm' : (2 : ℕ) • m = l := by
    change (2 : ℤ) • m = l at hm
    simpa only [two_smul] using hm
  rw [← hm']
  change RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form
    (F.integralLatticeEquiv.symm (2 • m)) w = _
  rw [map_nsmul]
  have h := RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy.polarizationAutomorphy_double_lattice (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding F.form (F.integralLatticeEquiv.symm m) w
  have he := F.latticeEmbedding_symm (2 • m)
  rw [map_nsmul] at he
  exact h.trans (congrArg (fun v : Fiber.ReferenceTangent s =>
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy ((1 / 2 : ℂ) • F.form) v w) he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
