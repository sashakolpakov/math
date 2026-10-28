import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Functions -/

namespace OAI.Analysis.DifferentialForms.Manifold.Functions

/-!
# Smooth complex-valued functions on a real normed space

The carrier consists of actual functions with mathlib's `ContDiff ℝ ∞`
property. It is the degree-zero coefficient space for the local de Rham
complex, not a replacement for forms on an algebraic variety.
-/

open scoped ContDiff

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex submodule of smooth complex-valued functions. -/
def smoothFunctions : Submodule ℂ (E → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : E => (0 : ℂ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    change ContDiff ℝ ∞ (fun x => f x + g x)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ (fun x => c • f x)
    exact hf.const_smul c

/-- A smooth complex-valued function on the underlying real normed space. -/
abbrev SmoothFunction := ↥(smoothFunctions E)

namespace SmoothFunction

variable {E}

instance : CoeFun (SmoothFunction E) (fun _ => E → ℂ) := ⟨Subtype.val⟩

/-- A bundled smooth function has the stated smoothness property. -/
theorem smooth (f : SmoothFunction E) : ContDiff ℝ ∞ (f : E → ℂ) := f.property

@[ext]
theorem ext {f g : SmoothFunction E} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

@[simp]
theorem zero_apply (x : E) : (0 : SmoothFunction E) x = 0 := rfl

@[simp]
theorem add_apply (f g : SmoothFunction E) (x : E) : (f + g) x = f x + g x := rfl

@[simp]
theorem smul_apply (c : ℂ) (f : SmoothFunction E) (x : E) : (c • f) x = c * f x := rfl

/-- The constant smooth function with a prescribed complex value. -/
def const (c : ℂ) : SmoothFunction E := ⟨fun _ => c, by
  change ContDiff ℝ ∞ (fun _ : E => c)
  exact contDiff_const⟩

@[simp]
theorem const_apply (c : ℂ) (x : E) : (const c : SmoothFunction E) x = c := rfl

end SmoothFunction

end OAI.Analysis.DifferentialForms.Manifold.Functions
