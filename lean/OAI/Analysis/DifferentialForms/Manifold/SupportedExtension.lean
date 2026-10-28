import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import Mathlib.Topology.Algebra.Support

/-! # Supported Extension -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Supported extension of smooth manifold forms

A local form can be multiplied by a smooth function whose topological support
lies in its domain and then extended by zero. Smoothness at boundary points
follows from the open complement of the scalar function's topological support.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

section

/-- A scalar supported inside a form's smoothness domain gives a globally
smooth product, including along the boundary of that domain. -/
theorem Algebra.IsSmoothManifoldFormOn.smulFunction_of_tsupport_subset {f : M → ℂ}
    {form : Manifold.Algebra.RawManifoldForm E M n} {U : Set M}
    (hform : Manifold.Algebra.IsSmoothManifoldFormOn form U) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f U) (hsupp : tsupport f ⊆ U) :
    Manifold.Algebra.IsSmoothManifoldFormOn (Manifold.Algebra.RawManifoldForm.smulFunction f form) univ := by
  let domains : Bool → Set M := fun b => if b then U else (tsupport f)ᶜ
  apply Manifold.Algebra.IsSmoothManifoldFormOn.of_openCover (U := domains)
  · intro b
    cases b
    · apply (Manifold.Algebra.IsSmoothManifoldFormOn.zero (E := E) (n := n) (domains false)).congr
      intro x hx
      have hx' : x ∉ tsupport f := hx
      change 0 = f x • form x
      rw [image_eq_zero_of_notMem_tsupport hx']
      exact (zero_smul ℂ (form x)).symm
    · exact hform.smulFunction hf
  · intro b
    cases b
    · exact (isClosed_tsupport f).isOpen_compl
    · exact hU
  · intro x
    by_cases hx : x ∈ U
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      exact fun hs => hx (hsupp hs)

end

variable {U : Opens M}

/-- Multiply a local form by a scalar supported in its domain and extend by zero. -/
def Open.SmoothOpenManifoldForm.supportedExtension (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (hsupp : tsupport f ⊆ (U : Set M)) :
    Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M n where
  toFun form := Manifold.Algebra.SmoothManifoldForm.ofSmooth
    (Manifold.Algebra.RawManifoldForm.smulFunction f form.extension)
    (form.smooth.smulFunction_of_tsupport_subset U.isOpen hf hsupp)
  map_add' form other := by
    apply Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    change f x • (form + other).extension x =
      f x • form.extension x + f x • other.extension x
    rw [Open.SmoothOpenManifoldForm.extension_add]
    exact smul_add (f x) (form.extension x) (other.extension x)
  map_smul' c form := by
    apply Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    change f x • (c • form).extension x = c • (f x • form.extension x)
    rw [Open.SmoothOpenManifoldForm.extension_smul]
    exact smul_comm (f x) c (form.extension x)

@[simp]
theorem Open.SmoothOpenManifoldForm.supportedExtension_apply (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) (x : M) :
    Open.SmoothOpenManifoldForm.supportedExtension f hf hsupp form x = f x • form.extension x := rfl

/-- On the original domain the extension has the specified pointwise values. -/
@[simp]
theorem Open.SmoothOpenManifoldForm.supportedExtension_apply_mem (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) (x : U) :
    Open.SmoothOpenManifoldForm.supportedExtension f hf hsupp form x = f x • form x := by
  rw [Open.SmoothOpenManifoldForm.supportedExtension_apply, Open.SmoothOpenManifoldForm.extension_apply]

/-- The product extension vanishes outside the scalar's topological support. -/
theorem Open.SmoothOpenManifoldForm.supportedExtension_eq_zero_of_notMem_tsupport (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) {x : M} (hx : x ∉ tsupport f) :
    Open.SmoothOpenManifoldForm.supportedExtension f hf hsupp form x = 0 := by
  rw [Open.SmoothOpenManifoldForm.supportedExtension_apply, image_eq_zero_of_notMem_tsupport hx]
  exact zero_smul ℂ (form.extension x)

/-- Restricting the extension back recovers the local scalar action. -/
theorem Open.SmoothOpenManifoldForm.onOpen_supportedExtension (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (U : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E U n) :
    Manifold.Algebra.SmoothManifoldForm.onOpen U (Open.SmoothOpenManifoldForm.supportedExtension f hf hsupp form) =
      Open.SmoothOpenManifoldForm.smulByFunction f hf form := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [Manifold.Algebra.SmoothManifoldForm.onOpen_apply, Open.SmoothOpenManifoldForm.supportedExtension_apply_mem,
    Open.SmoothOpenManifoldForm.smulByFunction_apply]

end

end OAI.Analysis.DifferentialForms.Manifold
