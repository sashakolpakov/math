import OAI.Analysis.HodgeTheory.Decomposition.Hermitian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Metric Fiber -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions

noncomputable section

/-! A separate normed copy of each genuine projective tangent-coordinate fiber.
Its norm is derived from the proved Hermitian metric; the manifold model keeps
its original norm. -/

open scoped _root_.Manifold

section Fiber

variable (E : Type*) [AddCommGroup E] [Module ℂ E]

/-- A type copy on which the specified positive Hermitian pairing defines the norm. -/
structure HermitianFiber (_ : InnerProductSpace.Core ℂ E) where
  val : E

variable (h : InnerProductSpace.Core ℂ E)

def hermitianFiberUnderlying : HermitianFiber E h ≃ E where
  toFun := HermitianFiber.val
  invFun := HermitianFiber.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance hermitianFiberAddCommGroup : AddCommGroup (HermitianFiber E h) :=
  (hermitianFiberUnderlying E h).addCommGroup

private def hermitianFiberAddEquiv : HermitianFiber E h ≃+ E where
  toEquiv := hermitianFiberUnderlying E h
  map_add' _ _ := rfl

instance hermitianFiberModule : Module ℂ (HermitianFiber E h) :=
  (hermitianFiberAddEquiv E h).module ℂ

/-- The copy is algebraically the original tangent-coordinate fiber. -/
def hermitianFiberEquiv : HermitianFiber E h ≃ₗ[ℂ] E :=
  (hermitianFiberAddEquiv E h).linearEquiv ℂ

instance hermitianFiberCore : InnerProductSpace.Core ℂ (HermitianFiber E h) where
  inner u v := h.inner u.val v.val
  conj_inner_symm u v := h.conj_inner_symm u.val v.val
  re_inner_nonneg u := h.re_inner_nonneg u.val
  add_left u v w := h.add_left u.val v.val w.val
  smul_left u v z := h.smul_left u.val v.val z
  definite u hu := by
    have hv : u.val = 0 := h.definite u.val hu
    cases u
    cases hv
    rfl

instance hermitianFiberNormedAddCommGroup : NormedAddCommGroup (HermitianFiber E h) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance hermitianFiberInnerProductSpace : InnerProductSpace ℂ (HermitianFiber E h) :=
  InnerProductSpace.ofCore _

instance hermitianFiberRealInnerProductSpace : InnerProductSpace ℝ (HermitianFiber E h) :=
  InnerProductSpace.complexToReal

instance hermitianFiberScalarTower : IsScalarTower ℝ ℂ (HermitianFiber E h) :=
  IsScalarTower.restrictScalars ℝ ℂ _

instance hermitianFiberFiniteDimensional [FiniteDimensional ℂ E] :
    FiniteDimensional ℂ (HermitianFiber E h) :=
  (hermitianFiberEquiv E h).symm.finiteDimensional

theorem hermitianFiber_inner (u v : HermitianFiber E h) :
    inner ℂ u v = h.inner (hermitianFiberEquiv E h u) (hermitianFiberEquiv E h v) := rfl

end Fiber

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (y : V.analyticModel) (hy : y ∈ e.target)

abbrev ProjectiveMetricFiber :=
  HermitianFiber V.analyticModel (Hermitian.Constructions.projectiveHermitianCore V e he y hy)

/-- The metric fiber and the original analytic model have equivalent finite-dimensional topologies. -/
def projectiveMetricFiberEquiv : ProjectiveMetricFiber V e he y hy ≃L[ℂ] V.analyticModel :=
  (hermitianFiberEquiv V.analyticModel (Hermitian.Constructions.projectiveHermitianCore V e he y hy)).toContinuousLinearEquiv

theorem projectiveMetricFiber_inner (u v : ProjectiveMetricFiber V e he y hy) :
    inner ℂ u v = KahlerMetric.Constructions.metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y)
      (projectiveMetricFiberEquiv V e he y hy u) (projectiveMetricFiberEquiv V e he y hy v) := rfl

theorem projectiveMetricFiber_norm_sq (u : ProjectiveMetricFiber V e he y hy) :
    ‖u‖ ^ 2 = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y
      (projectiveMetricFiberEquiv V e he y hy u) (projectiveMetricFiberEquiv V e he y hy u) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), projectiveMetricFiber_inner,
    KahlerMetric.Constructions.projectiveMetricHermitian_self V e he y hy]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions
