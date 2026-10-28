import OAI.Analysis.DifferentialForms.Manifold.Algebra
import Mathlib.Topology.Sets.Opens

/-! # Open -/

namespace OAI.Analysis.DifferentialForms.Manifold.Open

noncomputable section

/-!
# Smooth manifold-form sections on open subsets

A local section takes values in the actual tangent covector space at its point.
The zero extension is an auxiliary global field; only its chartwise smoothness
inside the open domain is required. All changes outside the domain are ignored
by the proved locality of `IsSmoothManifoldFormOn`.
-/

open Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Local sections of the alternating tangent covector bundle. -/
abbrev RawOpenManifoldForm (U : Opens M) (n : ℕ) :=
  ∀ x : U, TangentSpace 𝓘(ℝ, E) (x : M) [⋀^Fin n]→L[ℝ] ℂ

variable {E} {n : ℕ}

/-- An auxiliary global extension of a local tangent-covector section. -/
def openManifoldFormExtension (U : Opens M) (f : RawOpenManifoldForm E U n) :
    Algebra.RawManifoldForm E M n := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp]
theorem openManifoldFormExtension_apply (U : Opens M)
    (f : RawOpenManifoldForm E U n) (x : U) :
    openManifoldFormExtension U f x = f x := by
  simp [openManifoldFormExtension, x.property]

@[simp]
theorem openManifoldFormExtension_zero (U : Opens M) :
    openManifoldFormExtension U (0 : RawOpenManifoldForm E U n) = 0 := by
  classical
  funext x
  simp [openManifoldFormExtension]

@[simp]
theorem openManifoldFormExtension_add (U : Opens M)
    (f g : RawOpenManifoldForm E U n) :
    openManifoldFormExtension U (f + g) =
      openManifoldFormExtension U f + openManifoldFormExtension U g := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [openManifoldFormExtension, hx]

@[simp]
theorem openManifoldFormExtension_smul (U : Opens M) (c : ℂ)
    (f : RawOpenManifoldForm E U n) :
    openManifoldFormExtension U (c • f) = c • openManifoldFormExtension U f := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp [openManifoldFormExtension, hx]
  · simp only [openManifoldFormExtension, dite_eq_right hx, Pi.smul_apply]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) = c • (0 : ℂ)
    simp

variable (E) in
/-- Actual chartwise smooth local sections form a complex submodule. -/
def smoothOpenManifoldFormSubmodule (U : Opens M) (n : ℕ) :
    Submodule ℂ (RawOpenManifoldForm E U n) where
  carrier := {f | Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U f) (U : Set M)}
  zero_mem' := by
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U
      (0 : RawOpenManifoldForm E U n)) (U : Set M)
    rw [openManifoldFormExtension_zero]
    exact Algebra.IsSmoothManifoldFormOn.zero _
  add_mem' := by
    intro f g hf hg
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U f) (U : Set M) at hf
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U g) (U : Set M) at hg
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U (f + g)) (U : Set M)
    rw [openManifoldFormExtension_add]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U f) (U : Set M) at hf
    change Algebra.IsSmoothManifoldFormOn (openManifoldFormExtension U (c • f)) (U : Set M)
    rw [openManifoldFormExtension_smul]
    exact hf.const_smul c

variable (E) in
/-- A genuine smooth local differential form on an open manifold domain. -/
abbrev SmoothOpenManifoldForm (U : Opens M) (n : ℕ) :=
  ↥(smoothOpenManifoldFormSubmodule E U n)

namespace SmoothOpenManifoldForm

variable {U V W : Opens M}

instance : CoeFun (SmoothOpenManifoldForm E U n) (fun _ => RawOpenManifoldForm E U n) :=
  ⟨fun form => form.1⟩

def extension (form : SmoothOpenManifoldForm E U n) : Algebra.RawManifoldForm E M n :=
  openManifoldFormExtension U (form : RawOpenManifoldForm E U n)

theorem smooth (form : SmoothOpenManifoldForm E U n) :
    Algebra.IsSmoothManifoldFormOn form.extension (U : Set M) := form.2

@[simp]
theorem extension_apply (form : SmoothOpenManifoldForm E U n) (x : U) :
    form.extension x = form x := openManifoldFormExtension_apply U _ x

@[ext]
theorem ext {form other : SmoothOpenManifoldForm E U n}
    (h : ∀ x, form x = other x) : form = other := Subtype.ext (funext h)

@[simp] theorem zero_apply (x : U) : (0 : SmoothOpenManifoldForm E U n) x = 0 := rfl
@[simp] theorem add_apply (form other : SmoothOpenManifoldForm E U n) (x : U) :
    (form + other) x = form x + other x := rfl
@[simp] theorem smul_apply (c : ℂ) (form : SmoothOpenManifoldForm E U n) (x : U) :
    (c • form) x = c • form x := rfl

@[simp]
theorem extension_add (form other : SmoothOpenManifoldForm E U n) :
    (form + other).extension = form.extension + other.extension :=
  openManifoldFormExtension_add U _ _

@[simp]
theorem extension_smul (c : ℂ) (form : SmoothOpenManifoldForm E U n) :
    (c • form).extension = c • form.extension := openManifoldFormExtension_smul U _ _

/-- A field smooth on U defines a local section, independently of exterior values. -/
def ofRaw (U : Opens M) (f : Algebra.RawManifoldForm E M n)
    (hf : Algebra.IsSmoothManifoldFormOn f (U : Set M)) : SmoothOpenManifoldForm E U n :=
  ⟨fun x => f x, hf.congr fun x hx =>
    (openManifoldFormExtension_apply U (fun y : U => f y) ⟨x, hx⟩).symm⟩

@[simp]
theorem ofRaw_apply (f : Algebra.RawManifoldForm E M n)
    (hf : Algebra.IsSmoothManifoldFormOn f (U : Set M)) (x : U) :
    ofRaw U f hf x = f x := rfl

@[simp]
theorem ofRaw_extension (form : SmoothOpenManifoldForm E U n) :
    ofRaw U form.extension form.smooth = form := by
  apply SmoothOpenManifoldForm.ext
  intro x
  exact extension_apply form x

/-- The chosen extension agrees with its representative near every domain point. -/
theorem extension_ofRaw_eventuallyEq (f : Algebra.RawManifoldForm E M n)
    (hf : Algebra.IsSmoothManifoldFormOn f (U : Set M)) (x : U) :
    ∀ᶠ y in 𝓝 (x : M), (ofRaw U f hf).extension y = f y := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  exact extension_apply (ofRaw U f hf) ⟨y, hy⟩

/-- Restriction of actual tangent-covector sections to an open subdomain. -/
def restrict (h : V ≤ U) :
    SmoothOpenManifoldForm E U n →ₗ[ℂ] SmoothOpenManifoldForm E V n where
  toFun form := ⟨fun x => form ⟨x, h x.property⟩, (form.smooth.mono h).congr
    (fun x hx => (extension_apply form ⟨x, h hx⟩).trans
      (openManifoldFormExtension_apply V (fun y => form ⟨y, h y.property⟩)
        ⟨x, hx⟩).symm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrict_apply (h : V ≤ U) (form : SmoothOpenManifoldForm E U n) (x : V) :
    restrict h form x = form ⟨x, h x.property⟩ := rfl

@[simp]
theorem restrict_refl (form : SmoothOpenManifoldForm E U n) :
    restrict (le_refl U) form = form := by
  apply SmoothOpenManifoldForm.ext
  intro x
  rfl

theorem restrict_trans (hVU : V ≤ U) (hWV : W ≤ V)
    (form : SmoothOpenManifoldForm E U n) :
    restrict hWV (restrict hVU form) = restrict (hWV.trans hVU) form := by
  apply SmoothOpenManifoldForm.ext
  intro x
  rfl

/-- Restriction changes the extension only away from the smaller open domain. -/
theorem extension_restrict_eventuallyEq (h : V ≤ U)
    (form : SmoothOpenManifoldForm E U n) (x : V) :
    ∀ᶠ y in 𝓝 (x : M), (restrict h form).extension y = form.extension y := by
  filter_upwards [V.isOpen.mem_nhds x.property] with y hy
  exact (extension_apply (restrict h form) ⟨y, hy⟩).trans
    (extension_apply form ⟨y, h hy⟩).symm

end SmoothOpenManifoldForm

namespace SmoothManifoldForm

/-- A globally smooth manifold form restricts to a smooth local section. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (U : Opens M) : Algebra.SmoothManifoldForm E M n →ₗ[ℂ] SmoothOpenManifoldForm E U n where
  toFun form := SmoothOpenManifoldForm.ofRaw U (form : Algebra.RawManifoldForm E M n)
    (form.smooth.mono (subset_univ _))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_apply (U : Opens M) (form : Algebra.SmoothManifoldForm E M n) (x : U) :
    Algebra.SmoothManifoldForm.onOpen U form x = form x := rfl

theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen {U V : Opens M} (h : V ≤ U) (form : Algebra.SmoothManifoldForm E M n) :
    SmoothOpenManifoldForm.restrict h (Algebra.SmoothManifoldForm.onOpen U form) = Algebra.SmoothManifoldForm.onOpen V form := by
  apply SmoothOpenManifoldForm.ext
  intro x
  rfl

end SmoothManifoldForm

end

end OAI.Analysis.DifferentialForms.Manifold.Open
