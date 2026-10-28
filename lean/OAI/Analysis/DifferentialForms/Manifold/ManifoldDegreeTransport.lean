import OAI.Analysis.DifferentialForms.Manifold.Derivative
import OAI.Analysis.DifferentialForms.Manifold.DegreeTransport

/-! # Manifold Degree Transport -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-! Equality transport of actual manifold forms and compatibility with differentiation. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n m k : ℕ}

section

/-- Change only the natural-number degree index, using a proved equality. -/
def Algebra.RawManifoldForm.castDegree (h : n = m) (form : Algebra.RawManifoldForm E M n) : Algebra.RawManifoldForm E M m := h ▸ form

@[simp]
theorem Algebra.RawManifoldForm.castDegree_apply (h : n = m) (form : Algebra.RawManifoldForm E M n) (x : M)
    (v : Fin m → TangentSpace 𝓘(ℝ, E) x) :
    Algebra.RawManifoldForm.castDegree h form x v = form x (fun i => v (Fin.cast h i)) := by
  cases h
  rfl

@[simp]
theorem Algebra.RawManifoldForm.castDegree_inChart (h : n = m) (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (y : E) :
    (Algebra.RawManifoldForm.castDegree h form).inChart e y = Basic.FormValue.castDegree h (form.inChart e y) := by
  cases h
  rfl

@[simp]
theorem Algebra.RawManifoldForm.castDegree_self (h : n = n) (form : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm.castDegree h form = form := by
  cases h
  rfl

@[simp]
theorem Algebra.RawManifoldForm.castDegree_castDegree (h : n = m) (g : m = k) (form : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm.castDegree g (Algebra.RawManifoldForm.castDegree h form) = Algebra.RawManifoldForm.castDegree (h.trans g) form := by
  cases h
  cases g
  rfl

@[simp]
theorem Algebra.RawManifoldForm.castDegree_add (h : n = m) (form other : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm.castDegree h (form + other) = Algebra.RawManifoldForm.castDegree h form + Algebra.RawManifoldForm.castDegree h other := by
  cases h
  rfl

@[simp]
theorem Algebra.RawManifoldForm.castDegree_smul (h : n = m) (c : ℂ) (form : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm.castDegree h (c • form) = c • Algebra.RawManifoldForm.castDegree h form := by
  cases h
  rfl

end

/-- Canonical equality transport of a genuine smooth manifold form. -/
def Algebra.SmoothManifoldForm.castDegree (h : n = m) (form : Algebra.SmoothManifoldForm E M n) : Algebra.SmoothManifoldForm E M m := h ▸ form

@[simp]
theorem Algebra.SmoothManifoldForm.castDegree_coe (h : n = m) (form : Algebra.SmoothManifoldForm E M n) :
    (Algebra.SmoothManifoldForm.castDegree h form : Algebra.RawManifoldForm E M m) =
      Algebra.RawManifoldForm.castDegree h (form : Algebra.RawManifoldForm E M n) := by
  cases h
  rfl

@[simp]
theorem Algebra.SmoothManifoldForm.castDegree_self (h : n = n) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.castDegree h form = form := by
  cases h
  rfl

@[simp]
theorem Algebra.SmoothManifoldForm.castDegree_castDegree (h : n = m) (g : m = k) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.castDegree g (Algebra.SmoothManifoldForm.castDegree h form) = Algebra.SmoothManifoldForm.castDegree (h.trans g) form := by
  cases h
  cases g
  rfl

@[simp]
theorem Algebra.SmoothManifoldForm.castDegree_add (h : n = m) (form other : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.castDegree h (form + other) = Algebra.SmoothManifoldForm.castDegree h form + Algebra.SmoothManifoldForm.castDegree h other := by
  cases h
  rfl

@[simp]
theorem Algebra.SmoothManifoldForm.castDegree_smul (h : n = m) (c : ℂ) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.castDegree h (c • form) = c • Algebra.SmoothManifoldForm.castDegree h form := by
  cases h
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

@[simp]
theorem Algebra.SmoothManifoldForm.d_castDegree (h : n = m) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.castDegree h form) = Algebra.SmoothManifoldForm.castDegree (congrArg (fun l => l + 1) h) (Algebra.SmoothManifoldForm.d form) := by
  cases h
  rfl

end OAI.Analysis.DifferentialForms.Manifold
