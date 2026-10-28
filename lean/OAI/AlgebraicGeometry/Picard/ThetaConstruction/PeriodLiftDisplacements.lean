import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Period Lift Displacements -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.ThetaConstruction.PeriodLiftDisplacements.Geometric.AlgebraicPeriodModel

/-! Smooth local potentials on the actual ThetaConstruction algebraic period model.
Their holomorphic differences exponentiate to the original primitive
theta translation factors on the actual period-chart overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationPotential (a : DefinitionsIntegral.Tangent g) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.SmoothScalarForm.SmoothComplexOpenFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.localPeriodDomain p) where
  val q := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a (M.localPeriodLift p q.val)
  property := by
    intro q
    have hw : ContMDiffAt 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q :=
      (M.localPeriodLift_contMDiffAt p q.val q.property).comp q
        (contMDiff_subtype_val (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞) q)
    have hr : ContMDiffAt 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex hw
    have hp : ContDiff ℝ ∞ (fun w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space => RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a w) :=
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_contDiff T.riemannForm a
    exact hp.contMDiff.contMDiffAt.comp q hr

def _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationZeroForm (a : DefinitionsIntegral.Tangent g) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.localPeriodDomain p) 0 :=
  DivisorClass.Chern.Manifold.DolbeaultComparison.openManifoldZeroPure _ (DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm (M.localTranslationPotential a p))

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationZeroForm_value (a : DefinitionsIntegral.Tangent g)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : M.localPeriodDomain p)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) q.val) :
    (M.localTranslationZeroForm a p).val q v =
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a (M.localPeriodLift p q.val) :=
  DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply (M.localTranslationPotential a p) q v

def _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localPeriodDifference (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    LocallyConstant ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r) (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice where
  toFun q := (ProjectivePeriodData.Geometric.projectivePeriodData T).periodChartDifference (M.period.symm p) (M.period.symm r) (M.period.symm q.val)
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChartDifference_continuousOn
      (M.period.symm p) (M.period.symm r)).comp_continuous
      (M.period.symm.continuous.comp continuous_subtype_val)
    intro q
    exact q.property

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localPeriodDifference_value (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    (M.localPeriodDifference p r q).val = M.localPeriodLift r q.val - M.localPeriodLift p q.val :=
  (ProjectivePeriodData.Geometric.projectivePeriodData T).periodChartDifference_val
    (M.period.symm p) (M.period.symm r) (M.period.symm q.val) q.property

def _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationDifference (a : DefinitionsIntegral.Tangent g) (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :=
  DivisorClass.Chern.Manifold.DolbeaultComparison.locallyConstantComplexHolomorphic _
    ⟨fun q => (Real.pi : ℂ) * T.riemannForm (M.localPeriodDifference p r q).val a,
      (M.localPeriodDifference p r).isLocallyConstant.comp (fun l => (Real.pi : ℂ) * T.riemannForm l.val a)⟩

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationDifference_value (a : DefinitionsIntegral.Tangent g)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localTranslationDifference a p r q =
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a (M.localPeriodLift r q.val) -
        RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a (M.localPeriodLift p q.val) := by
  have hs : M.localPeriodLift p q.val + (M.localPeriodDifference p r q).val = M.localPeriodLift r q.val := by
    rw [M.localPeriodDifference_value]
    abel
  exact (RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_translation T.riemannForm a (M.localPeriodLift p q.val)
    (M.localPeriodDifference p r q).val).symm.trans
      (congrArg (fun w => RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a w -
        RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential T.riemannForm a (M.localPeriodLift p q.val)) hs)

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationDifference_exp (hE : E.transpose = -E) (a : DefinitionsIntegral.Tangent g)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    Complex.exp (M.localTranslationDifference a p r q) =
      (PolarizationFactor.Geometric.polarizationFactor T hE).value (M.localPeriodDifference p r q) (M.localPeriodLift p q.val + (show (ProjectivePeriodData.Geometric.projectivePeriodData T).space from a)) /
        (PolarizationFactor.Geometric.polarizationFactor T hE).value (M.localPeriodDifference p r q) (M.localPeriodLift p q.val) := by
  have h := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPotential_exponential_translation T.riemannForm (DefinitionsIntegral.Geometric.integralLatticeBasis T)
    (DefinitionsIntegral.Geometric.integralLatticeForm T) T.lattice.subtype a (M.localPeriodLift p q.val) (M.localPeriodDifference p r q)
  have ht := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_translation T.riemannForm a (M.localPeriodLift p q.val)
    (M.localPeriodDifference p r q).val
  exact (congrArg Complex.exp ht).symm.trans h

end AlgebraicGeometry.Picard.ThetaConstruction.PeriodLiftDisplacements.Geometric.AlgebraicPeriodModel

namespace AlgebraicGeometry.Picard.ThetaConstruction

/-! On the vector preimages of native period charts, the difference
between a vector and its chosen lift is an actual locally constant
lattice section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.periodDisplacement_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.periodDisplacement_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.vectorPeriod_add_period (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    M.vectorPeriod (w + l.val) = M.vectorPeriod w := by
  apply congrArg M.period
  apply (@QuotientAddGroup.eq_iff_sub_mem (ProjectivePeriodData.Geometric.projectivePeriodData T).space inferInstance
    (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice.toAddSubgroup inferInstance (w + l.val) w).mpr
  rw [show w + l.val - w = l.val by abel]
  exact l.property

def PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : Opens (ProjectivePeriodData.Geometric.projectivePeriodData T).space :=
  ⟨M.vectorPeriod ⁻¹' M.localPeriodDomain p, (M.localPeriodDomain p).isOpen.preimage M.vectorPeriod_contMDiff.continuous⟩

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDomain_cover (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    ∃ p, w ∈ M.liftedPeriodDomain p := ⟨M.vectorPeriod w, M.mem_localPeriodDomain (M.vectorPeriod w)⟩

def PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodPoint (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : M.liftedPeriodDomain p → M.localPeriodDomain p :=
  fun w => ⟨M.vectorPeriod w.val, w.property⟩

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodPoint_holomorphic (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ContMDiff 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) ∞ (M.liftedPeriodPoint p) := by
  apply (ContMDiff.subtypeVal_comp_iff (M.localPeriodDomain p) (M.liftedPeriodPoint p)).mp
  exact M.vectorPeriod_contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space)) (n := ∞))

def PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodVector (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : M.liftedPeriodDomain p → (ProjectivePeriodData.Geometric.projectivePeriodData T).space :=
  fun w => M.localPeriodLift p (M.vectorPeriod w.val)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodVector_holomorphic (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ContMDiff 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞ (M.liftedPeriodVector p) := by
  intro w
  exact (M.localPeriodLift_contMDiffAt p (M.vectorPeriod w.val) w.property).comp w
    ((M.vectorPeriod_contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space)) (n := ∞))) w)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDisplacement_mem (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : M.liftedPeriodDomain p) : w.val - M.liftedPeriodVector p w ∈ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice := by
  have h : (QuotientAddGroup.mk (M.liftedPeriodVector p w) : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus) =
      QuotientAddGroup.mk w.val :=
    M.period.injective (M.localPeriodLift_period p (M.vectorPeriod w.val) w.property)
  exact (@QuotientAddGroup.eq_iff_sub_mem (ProjectivePeriodData.Geometric.projectivePeriodData T).space inferInstance
    (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice.toAddSubgroup inferInstance w.val (M.liftedPeriodVector p w)).mp h.symm

def PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDisplacement (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    LocallyConstant (M.liftedPeriodDomain p) (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice where
  toFun w := ⟨w.val - M.liftedPeriodVector p w, M.liftedPeriodDisplacement_mem p w⟩
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.sub (M.liftedPeriodVector_holomorphic p).continuous

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDisplacement_value (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : M.liftedPeriodDomain p) :
    (M.liftedPeriodDisplacement p w).val = w.val - M.localPeriodLift p (M.vectorPeriod w.val) := rfl

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDisplacement_change (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) (hp : w ∈ M.liftedPeriodDomain p) (hr : w ∈ M.liftedPeriodDomain r) :
    (M.liftedPeriodDisplacement r ⟨w, hr⟩).val =
      (M.liftedPeriodDisplacement p ⟨w, hp⟩).val -
        (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val := by
  change w - M.localPeriodLift r (M.vectorPeriod w) =
    (w - M.localPeriodLift p (M.vectorPeriod w)) -
      (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val
  rw [M.localPeriodDifference_value]
  abel

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDomain_translate (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    w + l.val ∈ M.liftedPeriodDomain p ↔ w ∈ M.liftedPeriodDomain p := by
  change M.vectorPeriod (w + l.val) ∈ M.localPeriodDomain p ↔ M.vectorPeriod w ∈ M.localPeriodDomain p
  exact (congrArg (fun q => q ∈ M.localPeriodDomain p) (M.vectorPeriod_add_period l w)).to_iff

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedPeriodDisplacement_translate (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) (w : M.liftedPeriodDomain p) :
    (M.liftedPeriodDisplacement p
      ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩).val =
        (M.liftedPeriodDisplacement p w).val + l.val := by
  change w.val + l.val - M.localPeriodLift p (M.vectorPeriod (w.val + l.val)) =
    (w.val - M.localPeriodLift p (M.vectorPeriod w.val)) + l.val
  rw [M.vectorPeriod_add_period]
  abel

end AlgebraicGeometry.Picard.ThetaConstruction

end

end OAI
