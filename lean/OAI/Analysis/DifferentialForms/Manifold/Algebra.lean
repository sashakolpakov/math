import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Algebra -/

namespace OAI.Analysis.DifferentialForms.Manifold.Algebra

section

/-!
# Complex-valued differential forms on real charted manifolds

A field assigns a continuous alternating covector to the actual tangent space
at each point. Its chart expression pulls that covector back along the
derivative of the chart inverse. Smoothness is the usual smoothness of these
expressions on chart domains, rather than smoothness in the arbitrary preferred
tangent-space coordinates used to implement the tangent bundle.

The definitions make sense for a charted space; their manifold interpretation
uses a smooth atlas. Restriction and gluing below require only the local
definition and the topological properties of charts.
-/

open scoped _root_.Manifold ContDiff
open Set

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- An actual complex-valued alternating covector field on real tangent spaces. -/
abbrev RawManifoldForm (n : ℕ) :=
  ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ

variable {E M} {n : ℕ}

/-- Express a covector field in a chart by pulling back along its inverse.
The canonical identification of a vector-space tangent space with the vector
space is explicit. -/
noncomputable def RawManifoldForm.inChart (form : RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) : E → E [⋀^Fin n]→L[ℝ] ℂ :=
  fun y => (form (e.symm y)).compContinuousLinearMap
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).comp
      (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap)

/-- The portion of a chart where a form on `U` is expressed. -/
def manifoldFormChartDomain (e : OpenPartialHomeomorph M E) (U : Set M) : Set E :=
  e.target ∩ e.symm ⁻¹' U

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem isOpen_manifoldFormChartDomain (e : OpenPartialHomeomorph M E)
    {U : Set M} (hU : IsOpen U) : IsOpen (manifoldFormChartDomain e U) :=
  e.isOpen_inter_preimage_symm hU

/-- Smoothness of an actual alternating covector field, tested in every chart
of the chosen atlas on the specified domain. -/
def IsSmoothManifoldFormOn (form : RawManifoldForm E M n) (U : Set M) : Prop :=
  ∀ e ∈ atlas E M, ContDiffOn ℝ ∞ (form.inChart e) (manifoldFormChartDomain e U)

/-- A global smooth complex-valued differential form in the chartwise model. -/
abbrev SmoothManifoldForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] (n : ℕ) :=
  {form : RawManifoldForm E M n // IsSmoothManifoldFormOn form univ}

namespace IsSmoothManifoldFormOn

/-- Restriction of the domain preserves smoothness of the covector field. -/
theorem mono {form : RawManifoldForm E M n} {U V : Set M}
    (hform : IsSmoothManifoldFormOn form U) (hVU : V ⊆ U) :
    IsSmoothManifoldFormOn form V := by
  intro e he
  exact (hform e he).mono fun _ hy => ⟨hy.1, hVU hy.2⟩

/-- Smoothness depends only on the values of the field on its domain. -/
theorem congr {form other : RawManifoldForm E M n} {U : Set M}
    (hform : IsSmoothManifoldFormOn form U)
    (heq : ∀ x ∈ U, form x = other x) : IsSmoothManifoldFormOn other U := by
  intro e he
  apply (hform e he).congr
  intro y hy
  simp only [RawManifoldForm.inChart, heq (e.symm y) hy.2]

/-- Smoothness is local on an arbitrary union of open domains. -/
theorem iUnion {ι : Type*} {form : RawManifoldForm E M n} {U : ι → Set M}
    (hform : ∀ i, IsSmoothManifoldFormOn form (U i)) (hU : ∀ i, IsOpen (U i)) :
    IsSmoothManifoldFormOn form (⋃ i, U i) := by
  intro e he
  have hlocal := ContDiffOn.iUnion_of_isOpen
    (fun i => hform i e he) (fun i => isOpen_manifoldFormChartDomain e (hU i))
  simpa only [manifoldFormChartDomain, preimage_iUnion, inter_iUnion] using hlocal

/-- A field smooth on every member of an open cover is globally smooth. -/
theorem of_openCover {ι : Type*} {form : RawManifoldForm E M n} {U : ι → Set M}
    (hform : ∀ i, IsSmoothManifoldFormOn form (U i)) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : IsSmoothManifoldFormOn form univ := by
  have hUnion : (⋃ i, U i) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover x
  rw [← hUnion]
  exact iUnion hform hU

end IsSmoothManifoldFormOn

/-- Glue covector fields over a cover. Agreement on overlaps is used in the
gluing theorem below, so this definition does not depend mathematically on the
chosen index when that agreement holds. -/
noncomputable def glueRawManifoldForm {ι : Type*} (U : ι → Set M)
    (forms : ι → RawManifoldForm E M n) (hcover : ∀ x, ∃ i, x ∈ U i) :
    RawManifoldForm E M n :=
  fun x => forms (Classical.choose (hcover x)) x

theorem glueRawManifoldForm_eq {ι : Type*} (U : ι → Set M)
    (forms : ι → RawManifoldForm E M n) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → forms i x = forms j x)
    (i : ι) {x : M} (hx : x ∈ U i) :
    glueRawManifoldForm U forms hcover x = forms i x :=
  hcompat _ i x (Classical.choose_spec (hcover x)) hx

/-- Compatible smooth local covector fields glue to a globally smooth field. -/
theorem isSmooth_glueRawManifoldForm {ι : Type*} (U : ι → Set M)
    (forms : ι → RawManifoldForm E M n) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hU : ∀ i, IsOpen (U i)) (hforms : ∀ i, IsSmoothManifoldFormOn (forms i) (U i))
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → forms i x = forms j x) :
    IsSmoothManifoldFormOn (glueRawManifoldForm U forms hcover) univ := by
  apply IsSmoothManifoldFormOn.of_openCover (U := U) _ hU hcover
  intro i
  apply (hforms i).congr
  intro x hx
  exact (glueRawManifoldForm_eq U forms hcover hcompat i hx).symm

/-- The glued global field is uniquely determined by its restrictions. -/
theorem glueRawManifoldForm_unique {ι : Type*} (U : ι → Set M)
    (forms : ι → RawManifoldForm E M n) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → forms i x = forms j x)
    (form : RawManifoldForm E M n) (hform : ∀ i x, x ∈ U i → form x = forms i x) :
    form = glueRawManifoldForm U forms hcover := by
  funext x
  obtain ⟨i, hi⟩ := hcover x
  exact (hform i x hi).trans (glueRawManifoldForm_eq U forms hcover hcompat i hi).symm

end

noncomputable section

/-! Pointwise complex-linear algebra on actual smooth manifold covector fields. -/

open scoped _root_.Manifold ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

namespace RawManifoldForm

@[simp]
theorem inChart_zero (e : OpenPartialHomeomorph M E) :
    (0 : RawManifoldForm E M n).inChart e = 0 := by
  funext y
  ext v
  rfl

@[simp]
theorem inChart_add (form other : RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) :
    (form + other).inChart e = form.inChart e + other.inChart e := by
  funext y
  ext v
  rfl

@[simp]
theorem inChart_smul (c : ℂ) (form : RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) :
    (c • form).inChart e = c • form.inChart e := by
  funext y
  ext v
  rfl

end RawManifoldForm

namespace IsSmoothManifoldFormOn

theorem zero (U : Set M) :
    IsSmoothManifoldFormOn (0 : RawManifoldForm E M n) U := by
  intro e _
  rw [RawManifoldForm.inChart_zero]
  exact contDiffOn_const

theorem add {form other : RawManifoldForm E M n} {U : Set M}
    (hform : IsSmoothManifoldFormOn form U)
    (hother : IsSmoothManifoldFormOn other U) :
    IsSmoothManifoldFormOn (form + other) U := by
  intro e he
  rw [RawManifoldForm.inChart_add]
  exact (hform e he).add (hother e he)

theorem const_smul {form : RawManifoldForm E M n} {U : Set M}
    (hform : IsSmoothManifoldFormOn form U) (c : ℂ) :
    IsSmoothManifoldFormOn (c • form) U := by
  intro e he
  rw [RawManifoldForm.inChart_smul]
  exact (hform e he).const_smul c

end IsSmoothManifoldFormOn

/-- Smooth covector fields form a complex submodule of actual tangent covector fields. -/
def smoothManifoldFormSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] (n : ℕ) :
    Submodule ℂ (RawManifoldForm E M n) where
  carrier := {form | IsSmoothManifoldFormOn form univ}
  zero_mem' := IsSmoothManifoldFormOn.zero univ
  add_mem' := fun hform hother => hform.add hother
  smul_mem' := fun c _ hform => hform.const_smul c

namespace SmoothManifoldForm

instance : AddCommGroup (SmoothManifoldForm E M n) :=
  inferInstanceAs (AddCommGroup ↥(smoothManifoldFormSubmodule E M n))

instance : Module ℂ (SmoothManifoldForm E M n) :=
  inferInstanceAs (Module ℂ ↥(smoothManifoldFormSubmodule E M n))

instance : CoeFun (SmoothManifoldForm E M n) (fun _ => RawManifoldForm E M n) :=
  ⟨fun form => form.1⟩

/-- The stored smoothness condition is actual chartwise smoothness. -/
theorem smooth (form : SmoothManifoldForm E M n) :
    IsSmoothManifoldFormOn (form : RawManifoldForm E M n) univ := form.2

/-- Bundle a field whose chart expressions have been proved smooth. -/
def ofSmooth (form : RawManifoldForm E M n)
    (hform : IsSmoothManifoldFormOn form univ) : SmoothManifoldForm E M n :=
  ⟨form, hform⟩

@[simp]
theorem ofSmooth_apply (form : RawManifoldForm E M n)
    (hform : IsSmoothManifoldFormOn form univ) (x : M) :
    ofSmooth form hform x = form x := rfl

@[ext]
theorem ext {form other : SmoothManifoldForm E M n}
    (h : ∀ x, form x = other x) : form = other := Subtype.ext (funext h)

@[simp]
theorem zero_apply (x : M) : (0 : SmoothManifoldForm E M n) x = 0 := rfl

@[simp]
theorem add_apply (form other : SmoothManifoldForm E M n) (x : M) :
    (form + other) x = form x + other x := rfl

@[simp]
theorem neg_apply (form : SmoothManifoldForm E M n) (x : M) :
    (-form) x = -form x := rfl

@[simp]
theorem sub_apply (form other : SmoothManifoldForm E M n) (x : M) :
    (form - other) x = form x - other x := rfl

@[simp]
theorem smul_apply (c : ℂ) (form : SmoothManifoldForm E M n) (x : M) :
    (c • form) x = c • form x := rfl

/-- Evaluation at a point is complex-linear into its actual cotangent exterior power. -/
def eval (x : M) :
    SmoothManifoldForm E M n →ₗ[ℂ] (TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ) where
  toFun := fun form => form x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp]
theorem eval_apply (x : M) (form : SmoothManifoldForm E M n) :
    eval x form = form x := rfl

end SmoothManifoldForm

end

end OAI.Analysis.DifferentialForms.Manifold.Algebra
