import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-! # Smooth Scalar Form -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

noncomputable section

section

/-! Actual smooth scalar functions as zero-forms on the original manifold opens. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

abbrev SmoothComplexOpenFunction (U : Opens M) := C^∞⟮𝓘(ℝ, E), U; 𝓘(ℝ, ℂ), ℂ⟯

theorem smoothOpenScalarExtension_contMDiffOn {U : Opens M} (f : SmoothComplexOpenFunction (E := E) U) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f) (U : Set M) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
  have h : (fun y : U => Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f y.val) = f.val := by
    funext y
    exact Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f y
  rw [h]
  exact f.property ⟨x, hx⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothScalarOpenZeroForm {U : Opens M} (f : SmoothComplexOpenFunction (E := E) U) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f)
    (smoothOpenScalarExtension_contMDiffOn f)
    (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm E U (LocallyConstant.const U 1))

theorem smoothScalarOpenZeroForm_apply {U : Opens M} (f : SmoothComplexOpenFunction (E := E) U)
    (x : U) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x.val) : smoothScalarOpenZeroForm f x v = f x := by
  simp only [smoothScalarOpenZeroForm, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply,
    Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply, LocallyConstant.coe_const, Function.const_apply, mul_one]

def smoothScalarOpenZeroFormLinear (U : Opens M) :
    SmoothComplexOpenFunction (E := E) U →ₗ[ℝ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 where
  toFun := smoothScalarOpenZeroForm
  map_add' f g := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, ContinuousAlternatingMap.add_apply,
      smoothScalarOpenZeroForm_apply, smoothScalarOpenZeroForm_apply, smoothScalarOpenZeroForm_apply]
    rfl
  map_smul' z f := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change smoothScalarOpenZeroForm (z • f) x v = z • smoothScalarOpenZeroForm f x v
    rw [smoothScalarOpenZeroForm_apply, smoothScalarOpenZeroForm_apply]
    rfl

end

section

/-! Restriction and literal chart coordinates of actual smooth scalar zero-forms. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] {U V : Opens M}

def smoothComplexOpenFunctionRestrict (h : V ≤ U) (f : SmoothComplexOpenFunction (E := E) U) :
    SmoothComplexOpenFunction (E := E) V :=
  ⟨fun x => f ⟨x.val, h x.property⟩, f.property.comp (contMDiff_inclusion (I := 𝓘(ℝ, E)) h)⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smoothScalarOpenZeroForm_restrict (h : V ≤ U) (f : SmoothComplexOpenFunction (E := E) U) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (smoothScalarOpenZeroForm f) =
      smoothScalarOpenZeroForm (smoothComplexOpenFunctionRestrict h f) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change smoothScalarOpenZeroForm f ⟨x.val, h x.property⟩ v = _
  rw [smoothScalarOpenZeroForm_apply, smoothScalarOpenZeroForm_apply]
  rfl

theorem smoothScalarOpenZeroForm_inChart (f : SmoothComplexOpenFunction (E := E) U)
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ U) :
    (smoothScalarOpenZeroForm f).extension.inChart e y =
      constOfIsEmpty ℝ E (Fin 0) (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm y)) := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩]
  ext v
  exact (smoothScalarOpenZeroForm_apply f ⟨e.symm y, hy⟩ _).trans
    (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm y, hy⟩).symm

end

/-! Pointwise smooth scalar action on the original open manifold forms, with literal restriction and chart formulas. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {U V : Opens M} {n : ℕ}

def smoothScalarOpenFormMul (f : SmoothComplexOpenFunction (E := E) U) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f)
    (smoothOpenScalarExtension_contMDiffOn f)

theorem smoothScalarOpenFormMul_apply (f : SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (x : U) :
    smoothScalarOpenFormMul f a x = f x • a x := by
  rw [smoothScalarOpenFormMul, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply,
    Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply]

theorem smoothScalarOpenFormMul_restrict (h : V ≤ U) (f : SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (smoothScalarOpenFormMul f a) =
      smoothScalarOpenFormMul (smoothComplexOpenFunctionRestrict h f) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, smoothScalarOpenFormMul_apply,
    smoothScalarOpenFormMul_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply]
  rfl

theorem smoothScalarOpenFormMul_inChart (f : SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (e : OpenPartialHomeomorph M E)
    {y : E} (hy : e.symm y ∈ U) :
    (smoothScalarOpenFormMul f a).extension.inChart e y =
      Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm y) • a.extension.inChart e y := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    smoothScalarOpenFormMul_apply, Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm y, hy⟩]
  ext v
  rfl

def smoothComplexOpenFunctionMul (f g : SmoothComplexOpenFunction (E := E) U) :
    SmoothComplexOpenFunction (E := E) U :=
  ⟨fun x => f x * g x,
    (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).contMDiff.comp
      (f.property.prodMk_space g.property)⟩

theorem smoothScalarOpenZeroForm_mul (f g : SmoothComplexOpenFunction (E := E) U) :
    smoothScalarOpenZeroForm (smoothComplexOpenFunctionMul f g) =
      smoothScalarOpenFormMul f (smoothScalarOpenZeroForm g) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [smoothScalarOpenFormMul_apply, ContinuousAlternatingMap.smul_apply,
    smoothScalarOpenZeroForm_apply, smoothScalarOpenZeroForm_apply]
  rfl

theorem smoothOpenScalarExtension_chart_contDiff (f : SmoothComplexOpenFunction (E := E) U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    ContDiffOn ℝ ∞ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) (Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) := by
  have heSmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  exact ((smoothOpenScalarExtension_contMDiffOn f).comp (heSmooth.mono inter_subset_left)
    (fun _ hy => hy.2)).contDiffOn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
