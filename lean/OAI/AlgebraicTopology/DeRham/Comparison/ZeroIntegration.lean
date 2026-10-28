import OAI.AlgebraicTopology.DeRham.Comparison.ComplexNormalizedIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalLocalCochains
import OAI.AlgebraicTopology.DeRham.Comparison.DegreeZeroExactness
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Zero Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ZeroIntegration

noncomputable section

/-!
# Degree-zero normalization of actual cubical integration

The zero-dimensional product measure is the Dirac measure of mass one.
Consequently integration over a point is literal evaluation. Constants map
to the augmentation cochain, and closed smooth zero-forms on a real normed
vector space are exactly constant functions.
-/

open _root_.MeasureTheory Set OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped _root_.Topology

variable {m : ℕ}

/-- The zero-dimensional cube is its one-point ambient space. -/
theorem zero_cube_eq_univ :
    Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ => 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  constructor <;> intro i <;> exact Fin.elim0 i

/-- The genuine zero-dimensional Lebesgue product measure has mass one. -/
theorem volume_zero_cube :
    volume (Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ => 1)) = 1 := by
  rw [zero_cube_eq_univ, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

/-- Real integration of a zero-form over a zero-cube is evaluation. -/
theorem integrateForm_zero_cube (σ : StokesF.SingularCubeStokes.SmoothSingularCube 0 m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin 0]→L[ℝ] ℝ) :
    StokesF.SingularCubeStokes.integrateForm σ form = form (σ.toFun 0) 0 := by
  rw [StokesF.SingularCubeStokes.integrateForm, StokesF.Stokes.integral, StokesF.Stokes.unitCube, zero_cube_eq_univ, Measure.restrict_univ,
    Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), integral_dirac]
  change form (σ.toFun 0) _ = form (σ.toFun 0) 0
  exact congrArg (fun v => form (σ.toFun 0) v) (Subsingleton.elim _ _)

/-- The componentwise complex integral has the same degree-zero normalization. -/
theorem complexIntegrateForm_zero_cube (σ : StokesF.SingularCubeStokes.SmoothSingularCube 0 m)
    (form : Analysis.DifferentialForms.Manifold.Basic.RawForm (Fin m → ℝ) 0) :
    ComplexCubeIntegration.complexIntegrateForm σ form = form (σ.toFun 0) 0 := by
  apply Complex.ext
  · rw [ComplexCubeIntegration.complexIntegrateForm_re, integrateForm_zero_cube, Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm_apply]
  · rw [ComplexCubeIntegration.complexIntegrateForm_im, integrateForm_zero_cube, Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm_apply]

/-- Integration over the actual normalized chain of a point is evaluation. -/
@[simp]
theorem normalizedComplexIntegration_point (form : Analysis.DifferentialForms.Manifold.Basic.RawForm (Fin m → ℝ) 0)
    (x : Fin m → ℝ) :
    ComplexNormalizedIntegration.normalizedComplexIntegration form (CubicalLocalCochains.normalizedPointChain x) = form x 0 := by
  rw [CubicalLocalCochains.normalizedPointChain, ComplexNormalizedIntegration.normalizedComplexIntegration_single,
    complexIntegrateForm_zero_cube]
  rfl

/-- A constant zero-form integrates to its value times the raw augmentation. -/
theorem complexRawCubicalIntegration_const (c : ℂ)
    (chain : StokesF.SingularCubeStokes.SingularChain 0 m) :
    ComplexNormalizedIntegration.complexRawCubicalIntegration
      ((Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (Fin m → ℝ)).toZeroForm) chain =
        Finsupp.degree chain • c := by
  induction chain using Finsupp.induction with
  | zero => simp
  | single_add σ a chain hσ ha ih =>
      simp only [map_add, ComplexNormalizedIntegration.complexRawCubicalIntegration_single, complexIntegrateForm_zero_cube,
        Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.toZeroForm_apply, Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const_apply,
        Finsupp.degree_single, add_smul, ih]

/-- The constant zero-form yields precisely the actual normalized augmentation. -/
theorem normalizedComplexIntegration_const (c : ℂ)
    (chain : CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    ComplexNormalizedIntegration.normalizedComplexIntegration
      ((Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (Fin m → ℝ)).toZeroForm) chain =
        CubicalLocalCochains.normalizedCubicalAugmentation m chain • c := by
  obtain ⟨raw, rfl⟩ := (CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ_surjective chain
  rw [ComplexNormalizedIntegration.normalizedComplexIntegration_mkQ, CubicalLocalCochains.normalizedCubicalAugmentation_mk]
  exact complexRawCubicalIntegration_const c raw

/-- The augmentation identity also holds as an equality of linear maps. -/
theorem normalizedComplexIntegration_const_eq (c : ℂ) :
    ComplexNormalizedIntegration.normalizedComplexIntegration
      ((Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (Fin m → ℝ)).toZeroForm) =
        (LinearMap.toSpanSingleton ℤ ℂ c).comp (CubicalLocalCochains.normalizedCubicalAugmentation m) := by
  apply LinearMap.ext
  intro chain
  exact normalizedComplexIntegration_const c chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constant smooth zero-forms are closed. -/
theorem d_const_toZeroForm (c : ℂ) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d ((Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E).toZeroForm) = 0 := by
  apply (DegreeZeroExactness.d_toZeroForm_eq_zero_iff _).mpr
  exact IsLocallyConstant.const c

/-- Connectedness of a real vector space turns the checked local kernel
description into the literal constant function at any chosen point. -/
theorem closedZeroForm_eq_const (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0)
    (hform : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form = 0) (x₀ : E) :
    form = (Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const (form x₀ 0) : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E).toZeroForm := by
  have hlc := (DegreeZeroExactness.d_zeroForm_eq_zero_iff form).mp hform
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change form x v = form x₀ 0
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv]
  exact hlc.apply_eq_of_isPreconnected (convex_univ : Convex ℝ (Set.univ : Set E)).isPreconnected
    (Set.mem_univ x) (Set.mem_univ x₀)

/-- Evaluation is injective on the actual closed degree-zero forms. -/
theorem closedZeroForm_eval_injective (x₀ : E)
    (form otherForm : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0)
    (hform : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form = 0) (hother : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d otherForm = 0)
    (heval : form x₀ 0 = otherForm x₀ 0) : form = otherForm := by
  rw [closedZeroForm_eq_const form hform x₀, closedZeroForm_eq_const otherForm hother x₀,
    heval]

/-- Closed zero-forms on a real vector space are canonically its complex
constant values; the forward map is actual point evaluation. -/
def closedZeroFormEvalEquiv (x₀ : E) :
    LinearMap.ker (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 1) ≃ₗ[ℂ] ℂ where
  toFun form := form.1 x₀ 0
  invFun c := ⟨(Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E).toZeroForm,
    d_const_toZeroForm c⟩
  left_inv form := Subtype.ext (closedZeroForm_eq_const form.1 form.2 x₀).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem closedZeroFormEvalEquiv_apply (x₀ : E)
    (form : LinearMap.ker (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 1)) :
    closedZeroFormEvalEquiv x₀ form = form.1 x₀ 0 := rfl

@[simp]
theorem closedZeroFormEvalEquiv_symm_apply (x₀ : E) (c : ℂ) :
    ((closedZeroFormEvalEquiv x₀).symm c : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0) =
      (Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E).toZeroForm := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ZeroIntegration
