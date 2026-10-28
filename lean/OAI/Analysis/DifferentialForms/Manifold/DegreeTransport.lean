import OAI.Analysis.DifferentialForms.Manifold.Basic

/-! # Degree Transport -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-! Canonical transport of actual forms along equality of their degrees. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m k : ℕ}

section

/-- Change the degree index only by an equality. No permutation of tangent
arguments, and in particular no alternating sign, is introduced. -/
def Basic.FormValue.castDegree (h : n = m) (form : Basic.FormValue E n) : Basic.FormValue E m := h ▸ form

@[simp]
theorem Basic.FormValue.castDegree_apply (h : n = m) (form : Basic.FormValue E n) (v : Fin m → E) :
    Basic.FormValue.castDegree h form v = form (fun i => v (Fin.cast h i)) := by
  cases h
  rfl

@[simp]
theorem Basic.FormValue.castDegree_self (h : n = n) (form : Basic.FormValue E n) :
    Basic.FormValue.castDegree h form = form := by
  cases h
  rfl

@[simp]
theorem Basic.FormValue.castDegree_castDegree (h : n = m) (g : m = k) (form : Basic.FormValue E n) :
    Basic.FormValue.castDegree g (Basic.FormValue.castDegree h form) = Basic.FormValue.castDegree (h.trans g) form := by
  cases h
  cases g
  rfl

@[simp]
theorem Basic.FormValue.castDegree_add (h : n = m) (form other : Basic.FormValue E n) :
    Basic.FormValue.castDegree h (form + other) = Basic.FormValue.castDegree h form + Basic.FormValue.castDegree h other := by
  cases h
  rfl

@[simp]
theorem Basic.FormValue.castDegree_smul (h : n = m) (c : ℂ) (form : Basic.FormValue E n) :
    Basic.FormValue.castDegree h (c • form) = c • Basic.FormValue.castDegree h form := by
  cases h
  rfl

end

/-- Canonical equality transport, preserving the actual smooth form. -/
def Basic.SmoothForm.castDegree (h : n = m) (form : Basic.SmoothForm E n) : Basic.SmoothForm E m := h ▸ form

@[simp]
theorem Basic.SmoothForm.castDegree_apply (h : n = m) (form : Basic.SmoothForm E n) (x : E) :
    Basic.SmoothForm.castDegree h form x = Basic.FormValue.castDegree h (form x) := by
  cases h
  rfl

@[simp]
theorem Basic.SmoothForm.castDegree_self (h : n = n) (form : Basic.SmoothForm E n) :
    Basic.SmoothForm.castDegree h form = form := by
  cases h
  rfl

@[simp]
theorem Basic.SmoothForm.castDegree_castDegree (h : n = m) (g : m = k) (form : Basic.SmoothForm E n) :
    Basic.SmoothForm.castDegree g (Basic.SmoothForm.castDegree h form) = Basic.SmoothForm.castDegree (h.trans g) form := by
  cases h
  cases g
  rfl

@[simp]
theorem Basic.SmoothForm.castDegree_add (h : n = m) (form other : Basic.SmoothForm E n) :
    Basic.SmoothForm.castDegree h (form + other) = Basic.SmoothForm.castDegree h form + Basic.SmoothForm.castDegree h other := by
  cases h
  rfl

@[simp]
theorem Basic.SmoothForm.castDegree_smul (h : n = m) (c : ℂ) (form : Basic.SmoothForm E n) :
    Basic.SmoothForm.castDegree h (c • form) = c • Basic.SmoothForm.castDegree h form := by
  cases h
  rfl

end OAI.Analysis.DifferentialForms.Manifold
