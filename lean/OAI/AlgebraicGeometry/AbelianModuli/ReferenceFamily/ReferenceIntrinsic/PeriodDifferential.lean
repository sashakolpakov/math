import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Period Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The constructed reference period map has a unique complex-linear
lift into the native exponential tangent space, preserving the actual
integral lattice. Local native quotient charts supply holomorphicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

def Reference.Fiber.ReferenceAnalyticFiber.nativeComparisonTorus (F : Reference.Fiber.ReferenceAnalyticFiber P z) : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus where
  V := F.periodData.space
  rationalModule := inferInstanceAs (Module ℚ (Reference.Fiber.ReferenceTangent s))
  rationalTower := inferInstanceAs (IsScalarTower ℚ ℂ (Reference.Fiber.ReferenceTangent s))
  lattice := F.periodData.periodIntegerLattice
  full := F.periodData.periodIntegerLattice_full

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

variable (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeQuotientComparison : F.nativeComparisonTorus.Point ≃+ (Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian).Point :=
  M.periodAddEquiv.trans (Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeQuotientComparison_holomorphic : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic M.nativeQuotientComparison.toAddMonoidHom := by
  intro v
  let p := fun w : F.periodData.space =>
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Intrinsic.Maps.IntrinsicAlgebraicMaps.algebraization M.abelian).symm (M.vectorPeriod w)
  let e := HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian) (p v)
  let U := p ⁻¹' e.source
  let f := e ∘ p
  have hd : MDifferentiable 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) p :=
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable Intrinsic.Maps.IntrinsicAlgebraicMaps.algebraization M.abelian).comp
      (M.vectorPeriod_contMDiff.mdifferentiable (by simp))
  refine ⟨U, f, e.open_source.preimage hd.continuous,
    HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.mem_chart_source _ (p v), ?_, ?_⟩
  · intro w hw
    have hchart : p w ∈ (chartAt (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (p v)).source := hw
    have h := (mdifferentiableAt_iff_target_of_mem_source (f := p) hchart).mp (hd w)
    exact (mdifferentiableAt_iff_differentiableAt.mp h.2).differentiableWithinAt
  · intro w hw
    have h := e.left_inv hw
    rw [HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart_symm] at h
    exact h.symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.existsUnique_nativePeriodLift :
    ∃! L : F.periodData.space →ₗ[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian,
      Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := F.nativeComparisonTorus) (B := Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian) L ∧
      Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts M.nativeQuotientComparison.toAddMonoidHom L :=
  Geometry.ComplexTorus.BettiLattice.CM.Construction.holomorphic_linear_lift F.nativeComparisonTorus (Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian)
    M.nativeQuotientComparison.toAddMonoidHom M.nativeQuotientComparison_holomorphic

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift : F.periodData.space →ₗ[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  Classical.choose M.existsUnique_nativePeriodLift

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift_lattice (v : F.periodData.space) (hv : v ∈ F.periodData.periodIntegerLattice) :
    M.nativePeriodLift v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian :=
  (Classical.choose_spec M.existsUnique_nativePeriodLift).1.1 v hv

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift_exp (v : F.periodData.space) :
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.nativePeriodLift v) =
      M.vectorPeriod v := by
  have h := (Classical.choose_spec M.existsUnique_nativePeriodLift).1.2 v
  have H := congrArg (Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian) h
  change (Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian)
      ((Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).symm (M.periodAddEquiv (QuotientAddGroup.mk v))) =
    (Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian) (QuotientAddGroup.mk (M.nativePeriodLift v)) at H
  exact H.symm.trans ((Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).apply_symm_apply
    (Additive.ofMul (M.vectorPeriod v)))

end

section

/-! The native exponential comparison is the actual derivative of the
reference period map. Its integral lattice comparison is an equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodDiff_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodDiff_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodDiff_realLie :
    LieGroup 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup M.abelian

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativePeriodLift_eq_differential (v : F.periodData.space) :
    M.nativePeriodLift v = M.periodDifferential v := by
  let L : F.periodData.space →L[ℝ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
    M.nativePeriodLift.toContinuousLinearMap.restrictScalars ℝ
  let e := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  have he : e ∘ L = M.vectorPeriod := funext M.nativePeriodLift_exp
  have h₀ : HasMFDerivAt 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) e
      (L 0) (ContinuousLinearMap.id ℝ _) := by
    rw [L.map_zero]
    exact HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero
  have hc := h₀.comp (0 : F.periodData.space) L.hasMFDerivAt
  have hr : mfderiv 𝓘(ℝ, F.periodData.space) 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      M.vectorPeriod 0 v = L v := by
    rw [← he]
    exact congrArg (fun D : F.periodData.space →L[ℝ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian => D v) hc.mfderiv
  have hcomplex := ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex (x := (0 : F.periodData.space))
    (M.vectorPeriod_contMDiff.of_le (by simp)).contMDiffAt v
  have hd := congrArg (fun D : F.periodData.space →L[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian => D v)
    M.periodDifferential_eq
  exact hr.symm.trans (hcomplex.trans hd.symm)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.periodDifferential_exp (v : F.periodData.space) :
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.periodDifferential v) = M.vectorPeriod v :=
  (congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (M.nativePeriodLift_eq_differential v).symm).trans (M.nativePeriodLift_exp v)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.periodDifferential_lattice_iff (v : F.periodData.space) :
    M.periodDifferential v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian ↔ v ∈ F.periodData.periodIntegerLattice := by
  change HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.periodDifferential v) = 1 ↔ _
  rw [M.periodDifferential_exp]
  have h : M.periodAddEquiv (QuotientAddGroup.mk v) = 0 ↔
      (QuotientAddGroup.mk v : F.periodData.periodTorus) = 0 := M.periodAddEquiv.map_eq_zero_iff
  exact h.trans (QuotientAddGroup.eq_zero_iff v)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeLatticeEquiv : F.periodData.periodIntegerLattice ≃ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian where
  toFun v := ⟨M.periodDifferential v.val, (M.periodDifferential_lattice_iff v.val).mpr v.property⟩
  invFun v := ⟨M.periodDifferential.symm v.val, by
    apply (M.periodDifferential_lattice_iff _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using v.property⟩
  left_inv v := Subtype.ext (M.periodDifferential.symm_apply_apply v.val)
  right_inv v := Subtype.ext (M.periodDifferential.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (map_add M.periodDifferential v.val w.val)
  map_smul' n v := Subtype.ext (map_zsmul M.periodDifferential n v.val)

end

/-! The inverse native period map differentiates to the actual inverse
of the constructed period marking, over both complex and real scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.inversePeriodDiff_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.inversePeriodDiff_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.period_symm_one : M.period.symm 1 = 0 := by
  apply M.period.injective
  exact (M.period.apply_symm_apply 1).trans M.vectorPeriod_zero.symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.inversePeriodDifferential_apply (u : F.periodData.space) :
    mfderiv 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space)
      M.period.symm 1 (M.periodDifferential u) = u := by
  have he : M.period.symm ∘ M.period = id := funext M.period.symm_apply_apply
  have hd := mfderiv_comp (0 : F.periodData.periodTorus)
    (M.period.symm.contMDiff.mdifferentiableAt (x := M.period 0) (by simp))
    (M.period.contMDiff.mdifferentiableAt (x := (0 : F.periodData.periodTorus)) (by simp))
  rw [he, mfderiv_id] at hd
  have hv := congrArg (fun d : F.periodData.space →L[ℂ] F.periodData.space => d u) hd
  change u = mfderiv 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space)
    M.period.symm (M.period 0) (M.periodDifferential u) at hv
  have hp : M.period 0 = 1 := M.vectorPeriod_zero
  rw [hp] at hv
  exact hv.symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.inversePeriodRealDifferential_apply (u : F.periodData.space) :
    mfderiv 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℝ, F.periodData.space)
      M.period.symm 1 (M.periodDifferential u) = u := by
  have h := ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex (x := (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (M.period.symm.contMDiff.of_le (by simp)).contMDiffAt (M.periodDifferential u)
  exact h.trans (M.inversePeriodDifferential_apply u)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
