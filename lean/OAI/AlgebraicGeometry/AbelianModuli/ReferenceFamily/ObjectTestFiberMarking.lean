import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.SurfaceStratum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IsoPeriodInvariants
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank

/-! # Object Test Fiber Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ObjectTestFiberMarking.FinePELModel

noncomputable section

/-! An actual fine-moduli identification transports an arbitrary native
field marking to the test fiber. Its integral lattice, rational polarization,
Hodge kernel and ordered exponential labels are retained exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
attribute [local irreducible] Models.FinePELModel.complexTestFamily RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.ChernPairing.nativePolarizationForm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hy : y ≫ f = M.objectPoint hM κ B)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFiberIso : PEL.Objects.PELIso B ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)) :=
  Classical.choice (M.complexTestFamily_object_iso hM κ f B y hy)

variable (m : let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking :
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety :=
  letI := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  letI := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  m.trans (Polarized.IsoPeriodInvariants.levelIsoFieldEquiv B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized
    B.action ((M.complexTestFamily κ f).action.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).action)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.objectTestFieldMarking hM κ f B y hy m v =
      Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized (m v) := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.objectTestFieldMarking hM κ f B y hy m v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety ↔
        m v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)) := by
  rw [M.objectTestFieldMarking_apply]
  exact Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_integral B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized (m v)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized y
      (M.objectTestFieldMarking hM κ f B y hy m v) (M.objectTestFieldMarking hM κ f B y hy m w) =
        Intrinsic.ChernPairing.nativePolarizationForm B.polarized (m v) (m w) := by
  rw [M.objectTestFieldMarking_apply, M.objectTestFieldMarking_apply]
  unfold RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm
  exact Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_polarization B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized (m v) (m w)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_complex (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    ((M.objectTestFieldMarking hM κ f B y hy m).restrictScalars ℚ).toLinearMap.baseChange ℂ u =
      (Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized).toLinearMap.baseChange ℂ
        ((m.restrictScalars ℚ).toLinearMap.baseChange ℂ u) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  have h : ((M.objectTestFieldMarking hM κ f B y hy m).restrictScalars ℚ).toLinearMap =
      (Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized).toLinearMap.comp
        (m.restrictScalars ℚ).toLinearMap := by
    apply LinearMap.ext
    exact M.objectTestFieldMarking_apply hM κ f B y hy m
  dsimp only
  rw [h, LinearMap.baseChange_comp]
  rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_kernel (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    ((M.objectTestFieldMarking hM κ f B y hy m).restrictScalars ℚ).toLinearMap.baseChange ℂ u ∈
      (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety).ker ↔
        (m.restrictScalars ℚ).toLinearMap.baseChange ℂ u ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized))).ker := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  dsimp only
  rw [M.objectTestFieldMarking_complex]
  exact Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_kernel B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized _

attribute [local irreducible] Models.FinePELModel.objectTestFieldMarking in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_first_kernel (hP : P.IsAdmissible)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (u : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
    u ∈ ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action y s
      (M.objectTestFieldMarking hM κ f B y hy m) P hP).comp e₀.toLinearMap).ker ↔
      (m.restrictScalars ℚ).toLinearMap.baseChange ℂ
        (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP (e₀ u)) ∈
          (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian
            (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized))).ker := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) B.action
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized
    (M.complexTestFamily κ f).action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized
    (M.complexTestFamily κ f).action y
  simpa only [RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using M.objectTestFieldMarking_kernel hM κ f B y hy m
      (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP (e₀ u))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectTestFieldMarking_level (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) (r : ℝ)
    (hc : Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint B.polarized c =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized))).toOver) (r • (m v).val)) :
    RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level y (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y) c =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver)
        (r • (M.objectTestFieldMarking hM κ f B y hy m v).val) := by
  rw [M.objectTestFieldMarking_apply]
  have h := Polarized.IsoPeriodInvariants.levelIsoPeriodEquiv_level B.polarized ((M.complexTestFamily κ f).polarized.pullback y.left) (M.objectTestFiberIso hM κ f B y hy).polarized c r (m v) hc
  rw [Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint_pullback] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ObjectTestFiberMarking.FinePELModel
