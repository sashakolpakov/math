import OAI.Analysis.DifferentialForms.Manifold.Coefficients
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction

noncomputable section

/-! Conjugation of actual differential forms for the HodgeComparison Hodge comparison. -/

open scoped _root_.Manifold ContDiff
open Set
open _root_.CategoryTheory
open scoped Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

/-- Pointwise conjugation acts on the values of an actual tangent covector. -/
def conjugateRawForm (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n :=
  fun x => Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (form x)

@[simp]
theorem conjugateRawForm_apply (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (x : M) (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    conjugateRawForm form x v = star (form x v) := rfl

/-- Conjugation of values commutes with passage to any chart. -/
theorem conjugateRawForm_inChart (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) :
    (conjugateRawForm form).inChart e =
      Analysis.DifferentialForms.Manifold.Coefficients.Comparison.postcomposeForm Complex.conjCLE.toContinuousLinearMap (form.inChart e) := by
  funext y
  ext v
  rfl

theorem conjugateRawForm_smooth (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (conjugateRawForm form.val) univ := by
  intro e he
  rw [conjugateRawForm_inChart]
  exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℂ (Fin n)
    Complex.conjCLE.toContinuousLinearMap).contDiff.comp_contDiffOn (form.property e he)

/-- Conjugation preserves the smoothness of genuine manifold forms. -/
def conjugateSmoothForm (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  ⟨conjugateRawForm form.val, conjugateRawForm_smooth form⟩

@[simp]
theorem conjugateSmoothForm_apply (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (x : M) (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    conjugateSmoothForm form x v = star (form x v) := rfl

@[simp]
theorem conjugateSmoothForm_involutive (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    conjugateSmoothForm (conjugateSmoothForm form) = form := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  exact star_star _

@[simp]
theorem conjugateSmoothForm_zero :
    conjugateSmoothForm (0 : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  exact star_zero _

/-- The conjugation operation is semilinear for complex conjugation. -/
def conjugateSmoothFormMap :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₛₗ[starRingEnd ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n where
  toFun := conjugateSmoothForm
  map_add' form other := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    exact star_add _ _
  map_smul' c form := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    exact map_mul (starRingEnd ℂ) c (form x v)

section Real

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Exterior differentiation commutes with pointwise conjugation. -/
theorem d_conjugateSmoothForm (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (conjugateSmoothForm form) =
      conjugateSmoothForm (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source E x)
  have hd := (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.property e
    (chart_mem_atlas E x) hx).differentiableAt (by simp)
  ext v
  change extDeriv ((conjugateRawForm form.val).inChart e) (e x)
      (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x (v i)) =
    star (extDeriv (form.val.inChart e) (e x) (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x (v i)))
  rw [conjugateRawForm_inChart, Analysis.DifferentialForms.Manifold.Coefficients.Comparison.extDeriv_postcomposeForm _ _ hd]
  rfl

/-- Conjugation of a closed form is a closed form. -/
def conjugateClosedForm (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n :=
  ⟨conjugateSmoothForm form.val, by
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (conjugateSmoothForm form.val) = 0
    rw [d_conjugateSmoothForm, form.property, conjugateSmoothForm_zero]⟩

/-- Conjugation as a semilinear map on the actual space of closed forms. -/
def conjugateClosedFormMap :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n →ₛₗ[starRingEnd ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n where
  toFun := conjugateClosedForm
  map_add' form other := Subtype.ext (conjugateSmoothFormMap.map_add form.val other.val)
  map_smul' c form := Subtype.ext (conjugateSmoothFormMap.map_smulₛₗ c form.val)

/-- Conjugation of an exact one-form is the differential of the conjugate
of its primitive. -/
theorem conjugateClosedForm_boundary_one (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    conjugateClosedForm (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldBoundaryToClosed E M 1 form) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldBoundaryToClosed E M 1 (conjugateSmoothForm form) := by
  apply Subtype.ext
  exact (d_conjugateSmoothForm form).symm

/-- Conjugation preserves the exact one-forms. -/
theorem conjugateClosedForm_preserves_exact_one :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1 ≤
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1).comap conjugateClosedFormMap := by
  rintro _ ⟨form, rfl⟩
  exact ⟨conjugateSmoothForm form, (conjugateClosedForm_boundary_one form).symm⟩

/-- Conjugation therefore acts on closed one-forms modulo exact one-forms. -/
def conjugateDeRhamQuotientOne :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient E M 1 →ₛₗ[starRingEnd ℂ]
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient E M 1 :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1).mapQ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1)
    conjugateClosedFormMap conjugateClosedForm_preserves_exact_one

@[simp]
theorem conjugateDeRhamQuotientOne_mk (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) :
    conjugateDeRhamQuotientOne ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1).mkQ form) =
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M 1).mkQ (conjugateClosedForm form) := rfl

end Real

section Complex

variable [NormedSpace ℂ E]

/-- Conjugation exchanges the holomorphic and antiholomorphic tangent types. -/
theorem conjugateRawForm_holomorphic
    (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1)
    (hform : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 0 form) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 0 1 (conjugateRawForm form) := by
  intro x z v
  have h := congrArg star (hform x z v)
  simpa only [conjugateRawForm_apply, pow_one, pow_zero, inv_one, mul_one, one_mul,
    star_mul, star_inv₀, mul_comm] using h

/-- The inverse exchange follows from the same pointwise conjugation. -/
theorem conjugateRawForm_antiholomorphic
    (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1)
    (hform : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 0 1 form) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 0 (conjugateRawForm form) := by
  intro x z v
  have h := congrArg star (hform x z v)
  simpa only [conjugateRawForm_apply, pow_one, pow_zero, inv_one, mul_one, one_mul,
    star_mul, star_inv₀, star_star, mul_comm] using h

end Complex

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Pulling back a conjugated form to a cube conjugates the scalar integrand. -/
theorem cubePullback_conjugate_apply
    (cube : AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube F N n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n)
    (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) :
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback cube (conjugateSmoothForm form) x v =
      star (AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback cube form x v) := by
  rfl

/-- Actual smooth-simplex integration commutes with conjugation. -/
theorem simplexIntegration_conjugate
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex F N).toSSet _⦋n⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma (conjugateSmoothForm form) =
      star (AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma form) := by
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_integral,
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_integral]
  simp only [cubePullback_conjugate_apply]
  change (-1 : ℝ) ^ n •
    (∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
      (starRingEnd ℂ) (AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback
        (AlgebraicTopology.DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube sigma) form x (fun j => Pi.single j 1))) = _
  rw [integral_conj]
  exact (Complex.conjCLE.toContinuousLinearMap.map_smul ((-1 : ℝ) ^ n) _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction
