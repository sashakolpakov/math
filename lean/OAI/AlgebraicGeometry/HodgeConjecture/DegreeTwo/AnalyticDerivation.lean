import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Analytic Derivation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation.Constructions

noncomputable section

section

/-!
# DegreeTwo: analytic chart tangent vectors give actual algebra derivations

Differentiating evaluation of regular functions in a genuine affine chart
satisfies the algebraic Leibniz rule at the underlying complex point.
-/

open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

variable {S E : Type*} [CommRing S] [Algebra ℂ S]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [Algebra S ℂ] [IsScalarTower ℂ S ℂ]

variable (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
  (hx : ∀ a : S, algebraMap S ℂ a = x a)
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) E)
  (hxe : x ∈ e.source)
  (hd : ∀ a : S, DifferentiableAt ℂ (fun z => e.symm z a) (e x))

/-- The derivation at an actual complex point obtained from a chart tangent
vector by differentiating every regular evaluation function. -/
def analyticChartDerivation (v : E) : Derivation ℂ S ℂ where
  toFun a := fderiv ℂ (fun z => e.symm z a) (e x) v
  map_add' a b := by
    simp only [map_add]
    exact congrArg (fun L : E →L[ℂ] ℂ => L v) (fderiv_add (hd a) (hd b))
  map_smul' c a := by
    simp only [map_smul]
    exact congrArg (fun L : E →L[ℂ] ℂ => L v) (fderiv_const_smul (hd a) c)
  map_one_eq_zero' := by
    change fderiv ℂ (fun z => e.symm z (1 : S)) (e x) v = 0
    simp only [map_one, fderiv_const_apply, zero_apply]
  leibniz' a b := by
    change fderiv ℂ (fun z => e.symm z (a * b)) (e x) v =
      a • fderiv ℂ (fun z => e.symm z b) (e x) v +
      b • fderiv ℂ (fun z => e.symm z a) (e x) v
    simp only [map_mul]
    rw [fderiv_fun_mul (hd a) (hd b)]
    simp only [add_apply, smul_apply,
      e.left_inv hxe, Algebra.smul_def, hx]
    rfl

omit [IsScalarTower ℂ S ℂ] in
@[simp]
theorem analyticChartDerivation_apply (v : E) (a : S) :
    analyticChartDerivation x hx e hxe hd v a =
      fderiv ℂ (fun z => e.symm z a) (e x) v := rfl

/-- A standard-smooth presentation determines a derivation by its free
coordinate values, through the actual basis of Kähler differentials. -/
theorem derivation_eq_of_freeCoordinates
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι]
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (δ ε : Derivation ℂ S ℂ)
    (h : ∀ i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map, δ (P.val i.val) = ε (P.val i.val)) :
    δ = ε := by
  have heq : δ.liftKaehlerDifferential = ε.liftKaehlerDifferential := by
    apply P.basisKaehler.ext
    intro i
    simpa only [P.basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D] using h i
  ext a
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using
    DFunLike.congr_fun heq (KaehlerDifferential.D ℂ S a)

end

/-!
# DegreeTwo: every algebraic tangent derivation is realized in an analytic chart

The tangent vector consists of the derivation's values on the free chart
coordinates. The actual Kähler basis proves equality on every regular function.
-/

open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

variable {S ι σ : Type*} [CommRing S] [Algebra ℂ S]
  [Fintype ι] [Fintype σ] [DecidableEq ι]
  [Algebra S ℂ] [IsScalarTower ℂ S ℂ]
  (P : Algebra.SubmersivePresentation ℂ S ι σ)
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hx : ∀ a : S, algebraMap S ℂ a = x a)
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
  (hxe : x ∈ e.source)
  (hforward : ∀ y i, e y i = y (P.val i.val))
  (hd : ∀ a : S, DifferentiableAt ℂ (fun z => e.symm z a) (e x))

include hforward hxe in
omit [Fintype ι] [DecidableEq ι] [Algebra S ℂ] [IsScalarTower ℂ S ℂ] in
theorem chartCoordinate_fderiv (v : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ)
    (i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) :
    fderiv ℂ (fun z => e.symm z (P.val i.val)) (e x) v = v i := by
  have heq : (fun z => e.symm z (P.val i.val)) =ᶠ[𝓝 (e x)] (fun z => z i) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hxe)] with z hz
    exact (hforward (e.symm z) i).symm.trans (congrFun (e.right_inv hz) i)
  rw [heq.fderiv_eq, (hasFDerivAt_apply i (e x)).fderiv]
  rfl

include hx hxe hforward hd in
/-- The analytic differential evaluates on the coordinate vector of an
algebraic derivation to that derivation's value, for every regular function. -/
theorem chart_fderiv_eq_derivation (δ : Derivation ℂ S ℂ) (a : S) :
    fderiv ℂ (fun z => e.symm z a) (e x)
      (fun i => δ (P.val i.val)) = δ a := by
  let v : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ := fun i => δ (P.val i.val)
  have heq : analyticChartDerivation x hx e hxe hd v = δ := by
    apply derivation_eq_of_freeCoordinates P
    intro i
    exact chartCoordinate_fderiv P x e hxe hforward v i
  exact DFunLike.congr_fun heq a

include hx in
/-- A standard-smooth chart realizes all point derivations simultaneously
by actual complex tangent vectors. -/
theorem exists_standardSmooth_chart_realizing_derivations :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
      x ∈ e.source ∧
      (∀ y i, e y i = y (P.val i.val)) ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) ∧
      (∀ (δ : Derivation ℂ S ℂ) (a : S),
        fderiv ℂ (fun z => e.symm z a) (e x) (fun i => δ (P.val i.val)) = δ a) := by
  obtain ⟨e, hxe, hforward, hinverse⟩ := ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart P x
  refine ⟨e, hxe, hforward, hinverse, ?_⟩
  intro δ a
  apply chart_fderiv_eq_derivation P x hx e hxe hforward
  intro b
  exact ((hinverse b).differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hxe))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation.Constructions
