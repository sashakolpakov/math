import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules
import OAI.Analysis.DifferentialForms.Manifold.SectionCoordinates
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant

/-! # Zero Functions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ZeroFunctions

noncomputable section

/-! Actual holomorphic zero-forms are precisely the standard holomorphic functions. -/

open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def complexConstantZeroCovector : ℂ →L[ℂ] (E [⋀^Fin 0]→L[ℝ] ℂ) where
  toLinearMap :=
    { toFun := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  cont := (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).continuous

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicFunctionZeroForm (f : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯) : DeRhamComplex.forms E M 0 := by
  have hf (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
      ContDiffAt ℂ ∞ (fun z => f (e.symm z)) y := by
    have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
    exact ((f.property _).comp y hi).contDiffAt
  let s : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ofSmooth (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar f) (by
      intro e he y hy
      rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
      exact ((complexConstantZeroCovector (E := E)).contDiff.contDiffAt.comp y
        (hf e he hy.1)).restrict_scalars ℝ |>.contDiffWithinAt)
  let p : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 0 := ⟨s, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (E := E) _⟩
  refine ⟨p, (ChartCoefficients.mem_forms_iff_coefficients_complex p).mpr ?_⟩
  intro e he y hy
  change DifferentiableAt ℂ ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar f).inChart e) y
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
  exact ((complexConstantZeroCovector (E := E)).differentiableAt.comp y
    ((hf e he hy).differentiableAt (by simp)))

theorem holomorphicFunctionZeroForm_apply (f : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯)
    (x : M) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) :
    DeRhamComplex.inclusion E M 0 (holomorphicFunctionZeroForm f) x v = f x := rfl

variable [FiniteDimensional ℂ E]

theorem holomorphicZeroForm_scalar_contMDiff (a : DeRhamComplex.forms E M 0) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (fun x => DeRhamComplex.inclusion E M 0 a x 0) := by
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have hc := (ScalarCoefficients.form_scalarCoefficient_holomorphic a e he 0).contDiffAt
    (e.open_target.mem_nhds hy)
  have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hx
  apply (hc.contMDiffAt.comp x he').congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  change DeRhamComplex.inclusion E M 0 a y 0 = (DeRhamComplex.inclusion E M 0 a).val.inChart e (e y) 0
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero_apply, e.left_inv hy]

def holomorphicZeroFormFunction (a : DeRhamComplex.forms E M 0) : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯ :=
  ⟨fun x => DeRhamComplex.inclusion E M 0 a x 0, holomorphicZeroForm_scalar_contMDiff a⟩

def holomorphicZeroFormsFunctionEquiv :
    C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯ ≃ₗ[C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯] DeRhamComplex.forms E M 0 where
  toFun := holomorphicFunctionZeroForm
  invFun := holomorphicZeroFormFunction
  left_inv f := by apply ContMDiffMap.ext; intro x; rfl
  right_inv a := by
    apply HolomorphicPullback.inclusion_injective 0
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    change DeRhamComplex.inclusion E M 0 a x 0 = DeRhamComplex.inclusion E M 0 a x v
    congr 1
    exact Subsingleton.elim _ _
  map_add' f g := by
    apply HolomorphicPullback.inclusion_injective 0
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl
  map_smul' f g := by
    apply HolomorphicPullback.inclusion_injective 0
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ZeroFunctions
