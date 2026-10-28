import OAI.Analysis.DifferentialForms.Manifold.Basic
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth
import OAI.Analysis.DifferentialForms.Manifold.ComplexLinearity
import OAI.Analysis.DifferentialForms.Manifold.SquareZero
import Mathlib.Topology.Sets.Opens

/-! # Open D -/

namespace OAI.Analysis.DifferentialForms.Manifold.OpenD

/-!
# Smooth differential forms on open subsets of a real normed space

An open-domain form is an actual function on its domain, with values in the
continuous alternating forms on the ambient tangent space. Smoothness is tested
on its extension by zero, only at points inside the open domain. The locality
lemmas show that the extension does not affect either smoothness or the exterior
derivative there. Restriction and exterior differentiation are complex linear.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/-- An auxiliary total function for a coefficient function on an open set. -/
noncomputable def openFormExtension (U : Opens E) (f : U → Basic.FormValue E n) :
    Basic.RawForm E n := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp] theorem openFormExtension_apply (U : Opens E) (f : U → Basic.FormValue E n)
    (x : U) : openFormExtension U f x = f x := by
  simp [openFormExtension, x.property]

@[simp] theorem openFormExtension_zero (U : Opens E) :
    openFormExtension U (0 : U → Basic.FormValue E n) = 0 := by
  classical
  funext x
  simp [openFormExtension]

@[simp] theorem openFormExtension_add (U : Opens E) (f g : U → Basic.FormValue E n) :
    openFormExtension U (f + g) = openFormExtension U f + openFormExtension U g := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [openFormExtension, hx]

@[simp] theorem openFormExtension_smul (U : Opens E) (c : ℂ)
    (f : U → Basic.FormValue E n) :
    openFormExtension U (c • f) = c • openFormExtension U f := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp [openFormExtension, hx]
  · simp only [openFormExtension, dite_eq_right hx, Pi.smul_apply]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) = c • (0 : ℂ)
    simp

/-- Smooth coefficient functions on an open set form a complex submodule. -/
def smoothOpenFormSubmodule (U : Opens E) (n : ℕ) :
    Submodule ℂ (U → Basic.FormValue E n) where
  carrier := {f | ContDiffOn ℝ ∞ (openFormExtension U f) (U : Set E)}
  zero_mem' := by
    change ContDiffOn ℝ ∞ (openFormExtension U (0 : U → Basic.FormValue E n)) (U : Set E)
    rw [openFormExtension_zero]
    change ContDiffOn ℝ ∞ (fun _ : E => (0 : Basic.FormValue E n)) (U : Set E)
    exact contDiffOn_const
  add_mem' := by
    intro f g hf hg
    change ContDiffOn ℝ ∞ (openFormExtension U f) (U : Set E) at hf
    change ContDiffOn ℝ ∞ (openFormExtension U g) (U : Set E) at hg
    change ContDiffOn ℝ ∞ (openFormExtension U (f + g)) (U : Set E)
    rw [openFormExtension_add]
    change ContDiffOn ℝ ∞ (fun x => openFormExtension U f x + openFormExtension U g x)
      (U : Set E)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiffOn ℝ ∞ (openFormExtension U f) (U : Set E) at hf
    change ContDiffOn ℝ ∞ (openFormExtension U (c • f)) (U : Set E)
    rw [openFormExtension_smul]
    change ContDiffOn ℝ ∞ (fun x => c • openFormExtension U f x) (U : Set E)
    exact hf.const_smul c

/-- A smooth complex-valued real differential form on an actual open domain. -/
abbrev SmoothOpenForm (U : Opens E) (n : ℕ) := ↥(smoothOpenFormSubmodule U n)

namespace SmoothOpenForm

variable {U V W : Opens E}

instance : CoeFun (SmoothOpenForm U n) (fun _ => U → Basic.FormValue E n) :=
  ⟨fun form => form.1⟩

/-- The zero extension is only an auxiliary representative near the domain. -/
noncomputable def extension (form : SmoothOpenForm U n) : Basic.RawForm E n :=
  openFormExtension U (form : U → Basic.FormValue E n)

theorem smooth (form : SmoothOpenForm U n) :
    ContDiffOn ℝ ∞ form.extension (U : Set E) := form.2

@[simp] theorem extension_apply (form : SmoothOpenForm U n) (x : U) :
    form.extension x = form x := openFormExtension_apply U _ x

@[ext] theorem ext {form otherForm : SmoothOpenForm U n} (h : ∀ x, form x = otherForm x) : form = otherForm :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (x : U) : (0 : SmoothOpenForm U n) x = 0 := rfl

@[simp] theorem add_apply (form otherForm : SmoothOpenForm U n) (x : U) :
    (form + otherForm) x = form x + otherForm x := rfl

@[simp] theorem smul_apply (c : ℂ) (form : SmoothOpenForm U n) (x : U) :
    (c • form) x = c • form x := rfl

@[simp] theorem extension_add (form otherForm : SmoothOpenForm U n) :
    (form + otherForm).extension = form.extension + otherForm.extension := openFormExtension_add U _ _

@[simp] theorem extension_smul (c : ℂ) (form : SmoothOpenForm U n) :
    (c • form).extension = c • form.extension := openFormExtension_smul U _ _

/-- Any ambient coefficient function smooth on the domain defines a form. -/
noncomputable def ofRaw (U : Opens E) (f : Basic.RawForm E n)
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) : SmoothOpenForm U n :=
  ⟨fun x => f x, hf.congr fun x hx => openFormExtension_apply U _ ⟨x, hx⟩⟩

@[simp] theorem ofRaw_apply (f : Basic.RawForm E n)
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) : ofRaw U f hf x = f x := rfl

@[simp] theorem ofRaw_extension (form : SmoothOpenForm U n) :
    ofRaw U form.extension form.smooth = form := by
  apply SmoothOpenForm.ext
  intro x
  exact form.extension_apply x

/-- The auxiliary extension of a restricted raw form agrees with it locally. -/
theorem extension_ofRaw_eventuallyEq (f : Basic.RawForm E n)
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) :
    (ofRaw U f hf).extension =ᶠ[𝓝 (x : E)] f := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  exact SmoothOpenForm.extension_apply (ofRaw U f hf) ⟨y, hy⟩

/-- Restrict an open-domain form to a smaller open domain. -/
noncomputable def restrict (h : V ≤ U) : SmoothOpenForm U n →ₗ[ℂ] SmoothOpenForm V n where
  toFun form := ⟨fun x => form ⟨x, h x.property⟩, form.smooth.congr_mono
    (fun x hx => (openFormExtension_apply V (fun y => form ⟨y, h y.property⟩)
      ⟨x, hx⟩).trans (SmoothOpenForm.extension_apply form ⟨x, h hx⟩).symm) h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (h : V ≤ U) (form : SmoothOpenForm U n) (x : V) :
    restrict h form x = form ⟨x, h x.property⟩ := rfl

@[simp] theorem restrict_refl (form : SmoothOpenForm U n) : restrict (le_refl U) form = form := by
  apply SmoothOpenForm.ext
  intro x
  rfl

theorem restrict_trans (hVU : V ≤ U) (hWV : W ≤ V) (form : SmoothOpenForm U n) :
    restrict hWV (restrict hVU form) = restrict (hWV.trans hVU) form := by
  apply SmoothOpenForm.ext
  intro x
  rfl

/-- Restriction changes the extension only away from the smaller domain. -/
theorem extension_restrict_eventuallyEq (h : V ≤ U) (form : SmoothOpenForm U n) (x : V) :
    (restrict h form).extension =ᶠ[𝓝 (x : E)] form.extension := by
  filter_upwards [V.isOpen.mem_nhds x.property] with y hy
  exact (SmoothOpenForm.extension_apply (restrict h form) ⟨y, hy⟩).trans
    (SmoothOpenForm.extension_apply form ⟨y, h hy⟩).symm

/-- Exterior differentiation on an open domain, with complex coefficients. -/
noncomputable def d : SmoothOpenForm U n →ₗ[ℂ] SmoothOpenForm U (n + 1) where
  toFun form := ofRaw U (extDeriv form.extension)
    (ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen form.smooth U.isOpen (by simp))
  map_add' form otherForm := by
    apply SmoothOpenForm.ext
    intro x
    change extDeriv (form + otherForm).extension (x : E) =
      extDeriv form.extension (x : E) + extDeriv otherForm.extension (x : E)
    rw [extension_add]
    exact extDeriv_add
      ((form.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
      ((otherForm.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
  map_smul' c form := by
    apply SmoothOpenForm.ext
    intro x
    change extDeriv (c • form).extension (x : E) = c • extDeriv form.extension (x : E)
    rw [extension_smul]
    exact ComplexLinearity.extDeriv_complex_smul c form.extension x

@[simp] theorem d_apply (form : SmoothOpenForm U n) (x : U) :
    d form x = extDeriv form.extension (x : E) := rfl

/-- The local value of the derivative is independent of the chosen smooth representative. -/
theorem d_ofRaw_apply (f : Basic.RawForm E n) (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) :
    d (ofRaw U f hf) x = extDeriv f (x : E) :=
  (extension_ofRaw_eventuallyEq f hf x).extDeriv_eq

/-- Restriction commutes with exterior differentiation. -/
theorem restrict_d (h : V ≤ U) (form : SmoothOpenForm U n) :
    restrict h (d form) = d (restrict h form) := by
  apply SmoothOpenForm.ext
  intro x
  exact (extension_restrict_eventuallyEq h form x).extDeriv_eq.symm

/-- The exterior differential squares to zero on every open domain. -/
theorem d_squared (form : SmoothOpenForm U n) : d (d form) = 0 := by
  apply SmoothOpenForm.ext
  intro x
  change extDeriv (d form).extension (x : E) = 0
  have heq : (d form).extension =ᶠ[𝓝 (x : E)] extDeriv form.extension := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact SmoothOpenForm.extension_apply (d form) ⟨y, hy⟩
  rw [heq.extDeriv_eq]
  exact SquareZero.extDeriv_extDeriv_of_contDiffAt
    (form.smooth.contDiffAt (U.isOpen.mem_nhds x.property))

end SmoothOpenForm

namespace SmoothForm

/-- A global smooth form determines a form on each open domain. -/
noncomputable def _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.onOpen (U : Opens E) : Basic.SmoothForm E n →ₗ[ℂ] SmoothOpenForm U n where
  toFun form := SmoothOpenForm.ofRaw U (form : Basic.RawForm E n) form.smooth.contDiffOn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.onOpen_apply (U : Opens E) (form : Basic.SmoothForm E n) (x : U) :
    Basic.SmoothForm.onOpen U form x = form x := rfl

theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.restrict_onOpen {U V : Opens E} (h : V ≤ U) (form : Basic.SmoothForm E n) :
    SmoothOpenForm.restrict h (Basic.SmoothForm.onOpen U form) = Basic.SmoothForm.onOpen V form := by
  apply SmoothOpenForm.ext
  intro x
  rfl

end SmoothForm

end OAI.Analysis.DifferentialForms.Manifold.OpenD
