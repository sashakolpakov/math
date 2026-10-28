import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Basic -/

namespace OAI.Analysis.DifferentialForms.Manifold.Basic

/-!
# Smooth complex-valued real differential forms on a normed space

The tangent space of a real normed vector space is canonically the vector space
itself. A differential form is therefore a smoothly varying continuous real
alternating multilinear map. The coefficients are complex, and scalar
multiplication acts on these coefficients, not on the real tangent arguments.
-/

open scoped ContDiff

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The value of a complex-valued real differential form at one point. -/
abbrev FormValue (n : ℕ) := E [⋀^Fin n]→L[ℝ] ℂ

/-- An unbundled complex-valued real differential form. -/
abbrev RawForm (n : ℕ) := E → FormValue E n

/-- Actual infinitely differentiable forms form a complex linear subspace. -/
def smoothFormSubmodule (n : ℕ) : Submodule ℂ (RawForm E n) where
  carrier := {form | ContDiff ℝ ∞ form}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : E => (0 : FormValue E n))
    exact contDiff_const
  add_mem' := by
    intro form otherForm hform hotherForm
    change ContDiff ℝ ∞ form at hform
    change ContDiff ℝ ∞ otherForm at hotherForm
    change ContDiff ℝ ∞ (fun x => form x + otherForm x)
    exact hform.add hotherForm
  smul_mem' := by
    intro c form hform
    change ContDiff ℝ ∞ form at hform
    change ContDiff ℝ ∞ (fun x => c • form x)
    exact hform.const_smul c

/-- A bundled smooth complex-valued real differential form. -/
abbrev SmoothForm (n : ℕ) := ↥(smoothFormSubmodule E n)

namespace SmoothForm

variable {E} {n : ℕ}

instance : CoeFun (SmoothForm E n) (fun _ => RawForm E n) := ⟨fun form => form.1⟩

/-- The smoothness proof is part of the subtype, with its usual analytic meaning. -/
theorem smooth (form : SmoothForm E n) : ContDiff ℝ ∞ (form : RawForm E n) := form.2

/-- Bundle a genuinely smooth form. -/
def ofSmooth (form : RawForm E n) (hform : ContDiff ℝ ∞ form) : SmoothForm E n := ⟨form, hform⟩

@[simp] theorem ofSmooth_apply (form : RawForm E n) (hform : ContDiff ℝ ∞ form) (x : E) :
    ofSmooth form hform x = form x := rfl

@[ext] theorem ext {form otherForm : SmoothForm E n} (h : ∀ x, form x = otherForm x) : form = otherForm :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (x : E) : (0 : SmoothForm E n) x = 0 := rfl

@[simp] theorem add_apply (form otherForm : SmoothForm E n) (x : E) :
    (form + otherForm) x = form x + otherForm x := rfl

@[simp] theorem neg_apply (form : SmoothForm E n) (x : E) : (-form) x = -form x := rfl

@[simp] theorem sub_apply (form otherForm : SmoothForm E n) (x : E) :
    (form - otherForm) x = form x - otherForm x := rfl

@[simp] theorem smul_apply (c : ℂ) (form : SmoothForm E n) (x : E) :
    (c • form) x = c • form x := rfl

/-- Evaluation of a form at a point is complex linear. -/
def eval (x : E) : SmoothForm E n →ₗ[ℂ] FormValue E n where
  toFun := fun form => form x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem eval_apply (x : E) (form : SmoothForm E n) : eval x form = form x := rfl

end SmoothForm

end OAI.Analysis.DifferentialForms.Manifold.Basic
