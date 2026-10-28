import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Intrinsic Period Differential -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! The constructed reference period map has a unique complex-linear
lift into the native exponential tangent space, preserving the actual
integral lattice. Local native quotient charts supply holomorphicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}

def IntrinsicPeriodDifferential.Geometric.nativeComparisonTorus (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus where
  V := (ProjectivePeriodData.Geometric.projectivePeriodData F).space
  rationalModule := inferInstanceAs (Module ℚ (DefinitionsIntegral.Tangent dim))
  rationalTower := inferInstanceAs (IsScalarTower ℚ ℂ (DefinitionsIntegral.Tangent dim))
  lattice := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice
  full := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice_full

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

variable (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeQuotientComparison : (IntrinsicPeriodDifferential.Geometric.nativeComparisonTorus F).Point ≃+ (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian).Point :=
  M.periodAddEquiv.trans (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeQuotientComparison_holomorphic : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic M.nativeQuotientComparison.toAddMonoidHom := by
  intro v
  let p := fun w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space =>
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.algebraization M.abelian).symm (M.vectorPeriod w)
  let e := HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian) (p v)
  let U := p ⁻¹' e.source
  let f := e ∘ p
  have hd : MDifferentiable 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) p :=
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.algebraization M.abelian).comp
      (M.vectorPeriod_contMDiff.mdifferentiable (by simp))
  refine ⟨U, f, e.open_source.preimage hd.continuous,
    HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.mem_chart_source _ (p v), ?_, ?_⟩
  · intro w hw
    have hchart : p w ∈ (chartAt (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (p v)).source := hw
    have h := (mdifferentiableAt_iff_target_of_mem_source (f := p) hchart).mp (hd w)
    exact (mdifferentiableAt_iff_differentiableAt.mp h.2).differentiableWithinAt
  · intro w hw
    have h := e.left_inv hw
    rw [HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart_symm] at h
    exact h.symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.existsUnique_nativePeriodLift :
    ∃! L : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian,
      Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := (IntrinsicPeriodDifferential.Geometric.nativeComparisonTorus F)) (B := AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian) L ∧
      Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts M.nativeQuotientComparison.toAddMonoidHom L :=
  Geometry.ComplexTorus.BettiLattice.CM.Construction.holomorphic_linear_lift (IntrinsicPeriodDifferential.Geometric.nativeComparisonTorus F) (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.torus M.abelian)
    M.nativeQuotientComparison.toAddMonoidHom M.nativeQuotientComparison_holomorphic

def PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian :=
  Classical.choose M.existsUnique_nativePeriodLift

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift_lattice (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (hv : v ∈ (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice) :
    M.nativePeriodLift v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian :=
  (Classical.choose_spec M.existsUnique_nativePeriodLift).1.1 v hv

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift_exp (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.nativePeriodLift v) =
      M.vectorPeriod v := by
  have h := (Classical.choose_spec M.existsUnique_nativePeriodLift).1.2 v
  have H := congrArg (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian) h
  change (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian)
      ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).symm (M.periodAddEquiv (QuotientAddGroup.mk v))) =
    (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian) (QuotientAddGroup.mk (M.nativePeriodLift v)) at H
  exact H.symm.trans ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv M.abelian).apply_symm_apply
    (Additive.ofMul (M.vectorPeriod v)))

end

section

/-! The native exponential comparison is the actual derivative of the
reference period map. Its integral lattice comparison is an equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodDiff_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodDiff_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodDiff_realLie :
    LieGroup 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup M.abelian

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodLift_eq_differential (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    M.nativePeriodLift v = M.periodDifferential v := by
  let L : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian :=
    M.nativePeriodLift.toContinuousLinearMap.restrictScalars ℝ
  let e := HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  have he : e ∘ L = M.vectorPeriod := funext M.nativePeriodLift_exp
  have h₀ : HasMFDerivAt 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) e
      (L 0) (ContinuousLinearMap.id ℝ _) := by
    rw [L.map_zero]
    exact HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero
  have hc := h₀.comp (0 : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) L.hasMFDerivAt
  have hr : mfderiv 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      M.vectorPeriod 0 v = L v := by
    rw [← he]
    exact congrArg (fun D : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian => D v) hc.mfderiv
  have hcomplex := ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex (x := (0 : (ProjectivePeriodData.Geometric.projectivePeriodData F).space))
    (M.vectorPeriod_contMDiff.of_le (by simp)).contMDiffAt v
  have hd := congrArg (fun D : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian => D v)
    M.periodDifferential_eq
  exact hr.symm.trans (hcomplex.trans hd.symm)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodDifferential_exp (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.periodDifferential v) = M.vectorPeriod v :=
  (congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (M.nativePeriodLift_eq_differential v).symm).trans (M.nativePeriodLift_exp v)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodDifferential_lattice_iff (v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    M.periodDifferential v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian ↔ v ∈ (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice := by
  change HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.periodDifferential v) = 1 ↔ _
  rw [M.periodDifferential_exp]
  have h : M.periodAddEquiv (QuotientAddGroup.mk v) = 0 ↔
      (QuotientAddGroup.mk v : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) = 0 := M.periodAddEquiv.map_eq_zero_iff
  exact h.trans (QuotientAddGroup.eq_zero_iff v)

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeLatticeEquiv : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice ≃ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian where
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

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.inversePeriodDiff_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.inversePeriodDiff_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.period_symm_one : M.period.symm 1 = 0 := by
  apply M.period.injective
  exact (M.period.apply_symm_apply 1).trans M.vectorPeriod_zero.symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.inversePeriodDifferential_apply (u : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    mfderiv 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
      M.period.symm 1 (M.periodDifferential u) = u := by
  have he : M.period.symm ∘ M.period = id := funext M.period.symm_apply_apply
  have hd := mfderiv_comp (0 : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (M.period.symm.contMDiff.mdifferentiableAt (x := M.period 0) (by simp))
    (M.period.contMDiff.mdifferentiableAt (x := (0 : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)) (by simp))
  rw [he, mfderiv_id] at hd
  have hv := congrArg (fun d : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℂ] (ProjectivePeriodData.Geometric.projectivePeriodData F).space => d u) hd
  change u = mfderiv 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    M.period.symm (M.period 0) (M.periodDifferential u) at hv
  have hp : M.period 0 = 1 := M.vectorPeriod_zero
  rw [hp] at hv
  exact hv.symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.inversePeriodRealDifferential_apply (u : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
      M.period.symm 1 (M.periodDifferential u) = u := by
  have h := ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex (x := (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (M.period.symm.contMDiff.of_le (by simp)).contMDiffAt (M.periodDifferential u)
  exact h.trans (M.inversePeriodDifferential_apply u)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
