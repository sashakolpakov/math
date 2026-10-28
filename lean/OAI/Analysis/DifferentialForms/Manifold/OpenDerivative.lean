import OAI.Analysis.DifferentialForms.Manifold.Open
import OAI.Analysis.DifferentialForms.Manifold.LocalDerivative

/-! # Open Derivative -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Exterior differentiation of actual open-domain manifold forms

Only local smoothness of the section on its given open domain is used. The
auxiliary extension by zero can be nonsmooth outside that domain. Locality of
the raw operator proves independence from exterior values, compatibility with
restriction, and square-zero for the bundled differential.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ} {U V : Opens M}

section

/-- The actual local exterior derivative as a complex-linear map. -/
def Open.SmoothOpenManifoldForm.d : Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Open.SmoothOpenManifoldForm E U (n + 1) where
  toFun form := Open.SmoothOpenManifoldForm.ofRaw U form.extension.exteriorDerivative
    (form.extension.exteriorDerivative_smooth_on U.isOpen form.smooth)
  map_add' form other := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change (form + other).extension.exteriorDerivative (x : M) =
      form.extension.exteriorDerivative (x : M) + other.extension.exteriorDerivative (x : M)
    rw [Open.SmoothOpenManifoldForm.extension_add]
    exact form.extension.exteriorDerivative_add_on other.extension U.isOpen
      form.smooth other.smooth x.property
  map_smul' c form := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change (c • form).extension.exteriorDerivative (x : M) =
      c • form.extension.exteriorDerivative (x : M)
    rw [Open.SmoothOpenManifoldForm.extension_smul]
    exact congrFun (form.extension.exteriorDerivative_smul c) x

@[simp] theorem Open.SmoothOpenManifoldForm.d_apply (form : Open.SmoothOpenManifoldForm E U n) (x : U) :
    Open.SmoothOpenManifoldForm.d form x = form.extension.exteriorDerivative (x : M) := rfl

/-- The derivative is independent of an ambient representative of the local section. -/
theorem Open.SmoothOpenManifoldForm.d_ofRaw_apply (f : Algebra.RawManifoldForm E M n)
    (hf : Algebra.IsSmoothManifoldFormOn f (U : Set M)) (x : U) :
    Open.SmoothOpenManifoldForm.d (Open.SmoothOpenManifoldForm.ofRaw U f hf) x = f.exteriorDerivative (x : M) := by
  apply Algebra.RawManifoldForm.exteriorDerivative_congr_on _ _ U.isOpen _ x.property
  intro y hy
  exact Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.ofRaw U f hf) ⟨y, hy⟩

/-- Local exterior differentiation commutes with restricting the actual section. -/
theorem Open.SmoothOpenManifoldForm.restrict_d (h : V ≤ U) (form : Open.SmoothOpenManifoldForm E U n) :
    Open.SmoothOpenManifoldForm.restrict h (Open.SmoothOpenManifoldForm.d form) = Open.SmoothOpenManifoldForm.d (Open.SmoothOpenManifoldForm.restrict h form) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  symm
  apply Algebra.RawManifoldForm.exteriorDerivative_congr_on _ _ V.isOpen _ x.property
  intro y hy
  exact (Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.restrict h form) ⟨y, hy⟩).trans
    (Open.SmoothOpenManifoldForm.extension_apply form ⟨y, h hy⟩).symm

/-- On each chart domain, the derivative is the usual exterior derivative of coefficients. -/
theorem Open.SmoothOpenManifoldForm.d_inChart (form : Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Algebra.manifoldFormChartDomain e (U : Set M)) :
    (Open.SmoothOpenManifoldForm.d form).extension.inChart e y = extDeriv (form.extension.inChart e) y := by
  calc
    (Open.SmoothOpenManifoldForm.d form).extension.inChart e y = form.extension.exteriorDerivative.inChart e y := by
      unfold Algebra.RawManifoldForm.inChart
      rw [Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.d form) ⟨e.symm y, hy.2⟩]
      rfl
    _ = extDeriv (form.extension.inChart e) y :=
      form.extension.exteriorDerivative_inChart_on U.isOpen form.smooth e he hy

/-- The local exterior derivative squares to zero. -/
theorem Open.SmoothOpenManifoldForm.d_squared (form : Open.SmoothOpenManifoldForm E U n) : Open.SmoothOpenManifoldForm.d (Open.SmoothOpenManifoldForm.d form) = 0 := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  change (Open.SmoothOpenManifoldForm.d form).extension.exteriorDerivative (x : M) = 0
  have hlocal : (Open.SmoothOpenManifoldForm.d form).extension.exteriorDerivative (x : M) =
      form.extension.exteriorDerivative.exteriorDerivative (x : M) := by
    apply Algebra.RawManifoldForm.exteriorDerivative_congr_on _ _ U.isOpen _ x.property
    intro y hy
    exact Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.d form) ⟨y, hy⟩
  rw [hlocal]
  exact form.extension.exteriorDerivative_squared_on U.isOpen form.smooth x.property

end

/-- Global and local manifold exterior derivatives agree after restriction. -/
theorem Algebra.SmoothManifoldForm.onOpen_d (U : Opens M) (form : Algebra.SmoothManifoldForm E M n) :
    Open.SmoothOpenManifoldForm.d (Algebra.SmoothManifoldForm.onOpen U form) = Algebra.SmoothManifoldForm.onOpen U (Algebra.SmoothManifoldForm.d form) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  exact Open.SmoothOpenManifoldForm.d_ofRaw_apply (form : Algebra.RawManifoldForm E M n)
    (form.smooth.mono (subset_univ _)) x

end

end OAI.Analysis.DifferentialForms.Manifold
