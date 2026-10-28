import OAI.Analysis.DifferentialForms.Manifold.Open
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Function Multiplication -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Multiplication of manifold forms by smooth functions

The scalar action here is pointwise on the actual tangent covector spaces.
Its chart formula proves smoothness from mathlib's `ContMDiffOn` condition,
and the local action commutes with restriction of open domains.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

section

/-- Multiply each actual tangent covector by the value of a complex function. -/
def Algebra.RawManifoldForm.smulFunction (f : M → ℂ) (form : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm E M n := fun x => f x • form x

@[simp]
theorem Algebra.RawManifoldForm.smulFunction_apply (f : M → ℂ) (form : Algebra.RawManifoldForm E M n) (x : M) :
    Algebra.RawManifoldForm.smulFunction f form x = f x • form x := rfl

/-- In a chart the scalar is just the function composed with the inverse chart. -/
theorem Algebra.RawManifoldForm.inChart_smulFunction (f : M → ℂ) (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) :
    (Algebra.RawManifoldForm.smulFunction f form).inChart e =
      fun y => f (e.symm y) • form.inChart e y := by
  funext y
  ext v
  rfl

/-- The nonzero locus of a product is contained in the two nonzero loci. -/
theorem Algebra.RawManifoldForm.nonzero_smulFunction_subset (f : M → ℂ) (form : Algebra.RawManifoldForm E M n) :
    {x | Algebra.RawManifoldForm.smulFunction f form x ≠ 0} ⊆
      Function.support f ∩ {x | form x ≠ 0} := by
  intro x hx
  constructor
  · intro h
    apply hx
    change f x • form x = 0
    change f x = 0 at h
    rw [h]
    exact zero_smul ℂ (form x)
  · intro h
    apply hx
    change f x • form x = 0
    rw [h]
    exact smul_zero (A := TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ) (f x)

end

variable [IsManifold 𝓘(ℝ, E) ∞ M]

section

/-- Smooth scalar multiplication preserves the actual chartwise form condition. -/
theorem Algebra.IsSmoothManifoldFormOn.smulFunction {f : M → ℂ} {form : Algebra.RawManifoldForm E M n} {U : Set M}
    (hform : Algebra.IsSmoothManifoldFormOn form U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f U) :
    Algebra.IsSmoothManifoldFormOn (Algebra.RawManifoldForm.smulFunction f form) U := by
  intro e he
  rw [Algebra.RawManifoldForm.inChart_smulFunction]
  have heSmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  have hfChart : ContDiffOn ℝ ∞ (f ∘ e.symm) (Algebra.manifoldFormChartDomain e U) :=
    (hf.comp (heSmooth.mono inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  exact hfChart.smul (hform e he)

end

section

/-- A smooth scalar function acts complex-linearly on smooth manifold forms. -/
def Algebra.SmoothManifoldForm.smulByFunction (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Algebra.SmoothManifoldForm E M n where
  toFun form := Algebra.SmoothManifoldForm.ofSmooth (Algebra.RawManifoldForm.smulFunction f form)
    (form.smooth.smulFunction hf.contMDiffOn)
  map_add' form other := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    exact smul_add (f x) (form x) (other x)
  map_smul' c form := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    exact smul_comm (f x) c (form x)

@[simp]
theorem Algebra.SmoothManifoldForm.smulByFunction_apply (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)
    (form : Algebra.SmoothManifoldForm E M n) (x : M) :
    Algebra.SmoothManifoldForm.smulByFunction f hf form x = f x • form x := rfl

end

variable {U V : Opens M}

/-- A function smooth on the open domain acts on its genuine local forms. -/
def Open.SmoothOpenManifoldForm.smulByFunction (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M)) :
    Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Open.SmoothOpenManifoldForm E U n where
  toFun form := Open.SmoothOpenManifoldForm.ofRaw U (Algebra.RawManifoldForm.smulFunction f form.extension)
    (form.smooth.smulFunction hf)
  map_add' form other := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change f x • (form + other).extension x =
      f x • form.extension x + f x • other.extension x
    rw [Open.SmoothOpenManifoldForm.extension_add]
    exact smul_add (f x) (form.extension x) (other.extension x)
  map_smul' c form := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change f x • (c • form).extension x = c • (f x • form.extension x)
    rw [Open.SmoothOpenManifoldForm.extension_smul]
    exact smul_comm (f x) c (form.extension x)

@[simp]
theorem Open.SmoothOpenManifoldForm.smulByFunction_apply (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) (x : U) :
    Open.SmoothOpenManifoldForm.smulByFunction f hf form x = f x • form x := by
  change f x • form.extension x = f x • form x
  rw [Open.SmoothOpenManifoldForm.extension_apply]

/-- Pointwise scalar multiplication is compatible with restriction of forms. -/
theorem Open.SmoothOpenManifoldForm.restrict_smulByFunction (h : V ≤ U) (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) :
    Open.SmoothOpenManifoldForm.restrict h (Open.SmoothOpenManifoldForm.smulByFunction f hf form) =
      Open.SmoothOpenManifoldForm.smulByFunction f (hf.mono h) (Open.SmoothOpenManifoldForm.restrict h form) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [Open.SmoothOpenManifoldForm.restrict_apply, Open.SmoothOpenManifoldForm.smulByFunction_apply]

/-- The local action agrees with the restriction of the global one. -/
theorem Open.SmoothOpenManifoldForm.onOpen_smulByFunction (U : Opens M) (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.onOpen U (Algebra.SmoothManifoldForm.smulByFunction f hf form) =
      Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn (Algebra.SmoothManifoldForm.onOpen U form) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [Algebra.SmoothManifoldForm.onOpen_apply, Algebra.SmoothManifoldForm.smulByFunction_apply,
    Open.SmoothOpenManifoldForm.smulByFunction_apply]

end

end OAI.Analysis.DifferentialForms.Manifold
