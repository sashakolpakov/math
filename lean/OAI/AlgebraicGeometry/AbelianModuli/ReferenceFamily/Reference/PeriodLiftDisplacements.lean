import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.LocalPeriodCharts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Period Lift Displacements -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! Actual smooth local potentials on the native reference abelian
variety. Their holomorphic differences exponentiate to the original
theta translation factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.translationPotentials_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.translationPotentials_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def AlgebraicModel.ReferenceAlgebraicModel.localTranslationPotential (a : F.periodData.space)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.SmoothScalarForm.SmoothComplexOpenFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.localPeriodDomain p) where
  val q := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a (M.localPeriodLift p q.val)
  property := by
    intro q
    have hw : ContMDiffAt 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q :=
      (M.localPeriodLift_contMDiffAt p q.val q.property).comp q
        (contMDiff_subtype_val (I := 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞) q)
    have hr : ContMDiffAt 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℝ, F.periodData.space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex hw
    have hp : ContDiff ℝ ∞ (fun w : F.periodData.space => RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a w) :=
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_contDiff F.form a
    exact hp.contMDiff.contMDiffAt.comp q hr

def AlgebraicModel.ReferenceAlgebraicModel.localTranslationZeroForm (a : F.periodData.space)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.localPeriodDomain p) 0 :=
  DivisorClass.Chern.Manifold.DolbeaultComparison.openManifoldZeroPure _ (DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm (M.localTranslationPotential a p))

theorem AlgebraicModel.ReferenceAlgebraicModel.localTranslationZeroForm_value (a : F.periodData.space)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : M.localPeriodDomain p)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) q.val) :
    (M.localTranslationZeroForm a p).val q v =
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a (M.localPeriodLift p q.val) :=
  DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply (M.localTranslationPotential a p) q v

def AlgebraicModel.ReferenceAlgebraicModel.localPeriodDifference (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    LocallyConstant ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r) F.periodData.periodIntegerLattice where
  toFun q := F.periodData.periodChartDifference (M.period.symm p) (M.period.symm r) (M.period.symm q.val)
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply (F.periodData.periodChartDifference_continuousOn (M.period.symm p) (M.period.symm r)).comp_continuous
      (M.period.symm.continuous.comp continuous_subtype_val)
    intro q
    exact q.property

theorem AlgebraicModel.ReferenceAlgebraicModel.localPeriodDifference_value (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    (M.localPeriodDifference p r q).val = M.localPeriodLift r q.val - M.localPeriodLift p q.val :=
  F.periodData.periodChartDifference_val (M.period.symm p) (M.period.symm r) (M.period.symm q.val) q.property

def AlgebraicModel.ReferenceAlgebraicModel.localTranslationDifference (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :=
  DivisorClass.Chern.Manifold.DolbeaultComparison.locallyConstantComplexHolomorphic _
    ⟨fun q => (Real.pi : ℂ) * F.form (M.localPeriodDifference p r q).val a,
      (M.localPeriodDifference p r).isLocallyConstant.comp (fun l => (Real.pi : ℂ) * F.form l.val a)⟩

theorem AlgebraicModel.ReferenceAlgebraicModel.localTranslationDifference_value (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localTranslationDifference a p r q =
      RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a (M.localPeriodLift r q.val) -
        RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a (M.localPeriodLift p q.val) := by
  have hs : M.localPeriodLift p q.val + (M.localPeriodDifference p r q).val = M.localPeriodLift r q.val := by
    rw [M.localPeriodDifference_value]
    abel
  exact (RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_translation F.form a (M.localPeriodLift p q.val)
    (M.localPeriodDifference p r q).val).symm.trans
      (congrArg (fun w => RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a w -
        RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential F.form a (M.localPeriodLift p q.val)) hs)

theorem AlgebraicModel.ReferenceAlgebraicModel.localTranslationDifference_exp (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    Complex.exp (M.localTranslationDifference a p r q) =
      (F.polarizationFactor hP).value (M.localPeriodDifference p r q) (M.localPeriodLift p q.val + a) /
        (F.polarizationFactor hP).value (M.localPeriodDifference p r q) (M.localPeriodLift p q.val) := by
  have h := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPotential_exponential_translation F.form (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding a (M.localPeriodLift p q.val) (F.integralLatticeEquiv.symm (M.localPeriodDifference p r q))
  have ht := RepresentationTheory.Theta.Geometric.AntiholomorphicPotential.antiholomorphicPolarizationPotential_translation F.form a (M.localPeriodLift p q.val)
    (F.latticeEmbedding (F.integralLatticeEquiv.symm (M.localPeriodDifference p r q)))
  have he : (Real.pi : ℂ) * F.form
      (F.latticeEmbedding (F.integralLatticeEquiv.symm (M.localPeriodDifference p r q))) a =
      M.localTranslationDifference a p r q :=
    congrArg (fun v => (Real.pi : ℂ) * F.form v a) (F.latticeEmbedding_symm (M.localPeriodDifference p r q))
  exact (congrArg Complex.exp (ht.trans he)).symm.trans h

end

/-! On the vector preimages of native period charts, the difference
between a vector and its chosen lift is an actual locally constant
lattice section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.periodDisplacement_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.periodDisplacement_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod_add_period (l : F.periodData.periodIntegerLattice) (w : F.periodData.space) :
    M.vectorPeriod (w + l.val) = M.vectorPeriod w := by
  apply congrArg M.period
  apply (@QuotientAddGroup.eq_iff_sub_mem F.periodData.space inferInstance
    F.periodData.periodIntegerLattice.toAddSubgroup inferInstance (w + l.val) w).mpr
  rw [show w + l.val - w = l.val by abel]
  exact l.property

def AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : Opens F.periodData.space :=
  ⟨M.vectorPeriod ⁻¹' M.localPeriodDomain p, (M.localPeriodDomain p).isOpen.preimage M.vectorPeriod_contMDiff.continuous⟩

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDomain_cover (w : F.periodData.space) :
    ∃ p, w ∈ M.liftedPeriodDomain p := ⟨M.vectorPeriod w, M.mem_localPeriodDomain (M.vectorPeriod w)⟩

def AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodPoint (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : M.liftedPeriodDomain p → M.localPeriodDomain p :=
  fun w => ⟨M.vectorPeriod w.val, w.property⟩

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodPoint_holomorphic (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ContMDiff 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) ∞ (M.liftedPeriodPoint p) := by
  apply (ContMDiff.subtypeVal_comp_iff (M.localPeriodDomain p) (M.liftedPeriodPoint p)).mp
  exact M.vectorPeriod_contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, F.periodData.space)) (n := ∞))

def AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodVector (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : M.liftedPeriodDomain p → F.periodData.space :=
  fun w => M.localPeriodLift p (M.vectorPeriod w.val)

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodVector_holomorphic (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ContMDiff 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, F.periodData.space) ∞ (M.liftedPeriodVector p) := by
  intro w
  exact (M.localPeriodLift_contMDiffAt p (M.vectorPeriod w.val) w.property).comp w
    ((M.vectorPeriod_contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, F.periodData.space)) (n := ∞))) w)

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDisplacement_mem (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : M.liftedPeriodDomain p) : w.val - M.liftedPeriodVector p w ∈ F.periodData.periodIntegerLattice := by
  have h : (QuotientAddGroup.mk (M.liftedPeriodVector p w) : F.periodData.periodTorus) =
      QuotientAddGroup.mk w.val :=
    M.period.injective (M.localPeriodLift_period p (M.vectorPeriod w.val) w.property)
  exact (@QuotientAddGroup.eq_iff_sub_mem F.periodData.space inferInstance
    F.periodData.periodIntegerLattice.toAddSubgroup inferInstance w.val (M.liftedPeriodVector p w)).mp h.symm

def AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDisplacement (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    LocallyConstant (M.liftedPeriodDomain p) F.periodData.periodIntegerLattice where
  toFun w := ⟨w.val - M.liftedPeriodVector p w, M.liftedPeriodDisplacement_mem p w⟩
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.sub (M.liftedPeriodVector_holomorphic p).continuous

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDisplacement_value (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : M.liftedPeriodDomain p) :
    (M.liftedPeriodDisplacement p w).val = w.val - M.localPeriodLift p (M.vectorPeriod w.val) := rfl

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDisplacement_change (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (w : F.periodData.space) (hp : w ∈ M.liftedPeriodDomain p) (hr : w ∈ M.liftedPeriodDomain r) :
    (M.liftedPeriodDisplacement r ⟨w, hr⟩).val =
      (M.liftedPeriodDisplacement p ⟨w, hp⟩).val -
        (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val := by
  change w - M.localPeriodLift r (M.vectorPeriod w) =
    (w - M.localPeriodLift p (M.vectorPeriod w)) -
      (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val
  rw [M.localPeriodDifference_value]
  abel

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDomain_translate (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (l : F.periodData.periodIntegerLattice) (w : F.periodData.space) :
    w + l.val ∈ M.liftedPeriodDomain p ↔ w ∈ M.liftedPeriodDomain p := by
  change M.vectorPeriod (w + l.val) ∈ M.localPeriodDomain p ↔ M.vectorPeriod w ∈ M.localPeriodDomain p
  exact (congrArg (fun q => q ∈ M.localPeriodDomain p) (M.vectorPeriod_add_period l w)).to_iff

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedPeriodDisplacement_translate (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (l : F.periodData.periodIntegerLattice) (w : M.liftedPeriodDomain p) :
    (M.liftedPeriodDisplacement p
      ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩).val =
        (M.liftedPeriodDisplacement p w).val + l.val := by
  change w.val + l.val - M.localPeriodLift p (M.vectorPeriod (w.val + l.val)) =
    (w.val - M.localPeriodLift p (M.vectorPeriod w.val)) + l.val
  rw [M.vectorPeriod_add_period]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
