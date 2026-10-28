import OAI.AlgebraicTopology.DeRham.Comparison.DegreeZeroExactness
import OAI.Analysis.DifferentialForms.Manifold.OpenD
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Locally Constant Zero Forms -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms

noncomputable section

/-!
# Locally constant functions are the closed smooth zero-forms

All sections in this file are functions on genuine open subsets. The map
from locally constant functions to smooth zero-forms is explicit, injective,
commutes with restriction, and has image exactly the actual differential's
kernel. This is the degree-zero exactness of the prospective de Rham sheaf
resolution; no positive-degree Poincare lemma is assumed.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar function on an open set, extended by zero only for differentiation. -/
def openScalarExtension (U : Opens E) (f : U → ℂ) : E → ℂ := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

omit [NormedSpace ℝ E] in
@[simp]
theorem openScalarExtension_apply (U : Opens E) (f : U → ℂ) (x : U) :
    openScalarExtension U f x = f x := by
  simp [openScalarExtension, x.property]

/-- A locally constant section has a genuinely smooth local extension. -/
theorem openScalarExtension_smooth (U : Opens E) (f : LocallyConstant U ℂ) :
    ContDiffOn ℝ ∞ (openScalarExtension U f) (U : Set E) := by
  apply DegreeZeroExactness.contDiffOn_of_isLocallyConstant_on_open U.isOpen
  change IsLocallyConstant (fun x : U => openScalarExtension U f x)
  have hf : IsLocallyConstant (fun x : U => f x) := f.isLocallyConstant
  simpa only [openScalarExtension_apply] using hf

/-- The scalar function underlying a zero-form, in its auxiliary ambient extension. -/
def zeroFormScalarExtension {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) : E → ℂ :=
  fun x => form.extension x 0

@[simp]
theorem zeroFormScalarExtension_apply {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) (x : U) :
    zeroFormScalarExtension form x = form x 0 := by
  simp [zeroFormScalarExtension]

theorem zeroFormScalarExtension_smooth {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) :
    ContDiffOn ℝ ∞ (zeroFormScalarExtension form) (U : Set E) := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).symm.contDiff.comp_contDiffOn
    form.smooth

theorem zeroFormScalarExtension_reconstruct {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) :
    (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0)
      (zeroFormScalarExtension form x)) = form.extension := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  change form.extension x 0 = form.extension x v
  congr 1
  exact Subsingleton.elim _ _

/-- The actual open-domain differential agrees with the scalar derivative in degree zero. -/
theorem d_openZeroForm_apply {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0)
    (x : U) (v : Fin 1 → E) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form x v =
      fderiv ℝ (zeroFormScalarExtension form) (x : E) (v 0) := by
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_apply, ← zeroFormScalarExtension_reconstruct form,
    extDeriv_constOfIsEmpty]
  rfl

/-- Closed smooth zero-forms on any open domain are exactly locally constant scalar sections. -/
theorem d_openZeroForm_eq_zero_iff {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0 ↔ IsLocallyConstant (fun x : U => form x 0) := by
  have hf := (zeroFormScalarExtension_smooth form).differentiableOn (by simp)
  rw [← show IsLocallyConstant (fun x : U => zeroFormScalarExtension form x) ↔
    IsLocallyConstant (fun x : U => form x 0) by simp only [zeroFormScalarExtension_apply]]
  have hcriterion : (∀ x ∈ U, fderiv ℝ (zeroFormScalarExtension form) x = 0) ↔
      IsLocallyConstant (fun x : U => zeroFormScalarExtension form x) :=
    DegreeZeroExactness.fderiv_eq_zero_on_open_iff U.isOpen hf
  rw [← hcriterion]
  constructor
  · intro h x hx
    apply ContinuousLinearMap.ext
    intro v
    have heval := congrArg (fun a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1 => a ⟨x, hx⟩ (fun _ => v)) h
    simpa only [d_openZeroForm_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, zero_apply] using heval
  · intro h
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [d_openZeroForm_apply, h x x.property, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, zero_apply]

/-- A locally constant scalar section defines its usual smooth zero-form. -/
def locallyConstantZeroForm (U : Opens E) (f : LocallyConstant U ℂ) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U
    (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (openScalarExtension U f x))
    ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn
      (openScalarExtension_smooth U f))

@[simp]
theorem locallyConstantZeroForm_apply (U : Opens E) (f : LocallyConstant U ℂ)
    (x : U) (v : Fin 0 → E) : locallyConstantZeroForm U f x v = f x := by
  change openScalarExtension U f x = f x
  exact openScalarExtension_apply U f x

/-- The degree-zero inclusion is complex linear. -/
def locallyConstantToZeroForm (U : Opens E) : LocallyConstant U ℂ →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 where
  toFun := locallyConstantZeroForm U
  map_add' f g := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [locallyConstantZeroForm_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.add_apply,
      ContinuousAlternatingMap.add_apply]
    rfl
  map_smul' c f := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [locallyConstantZeroForm_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.smul_apply,
      ContinuousAlternatingMap.smul_apply]
    rfl

@[simp]
theorem locallyConstantToZeroForm_apply (U : Opens E) (f : LocallyConstant U ℂ)
    (x : U) (v : Fin 0 → E) : locallyConstantToZeroForm U f x v = f x :=
  locallyConstantZeroForm_apply U f x v

theorem locallyConstantToZeroForm_injective (U : Opens E) :
    Function.Injective (locallyConstantToZeroForm U) := by
  intro f g h
  apply DFunLike.ext
  intro x
  have heval := congrArg (fun form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 => form x 0) h
  simpa only [locallyConstantToZeroForm_apply] using heval

@[simp]
theorem d_locallyConstantToZeroForm (U : Opens E) (f : LocallyConstant U ℂ) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (locallyConstantToZeroForm U f) = 0 := by
  rw [d_openZeroForm_eq_zero_iff]
  have hf : IsLocallyConstant (fun x : U => f x) := f.isLocallyConstant
  simpa only [locallyConstantToZeroForm_apply] using hf

/-- Exactness is proved as equality of the actual image and actual kernel. -/
theorem range_locallyConstantToZeroForm (U : Opens E) :
    LinearMap.range (locallyConstantToZeroForm U) =
      LinearMap.ker (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) := by
  ext form
  constructor
  · rintro ⟨f, rfl⟩
    exact d_locallyConstantToZeroForm U f
  · intro h
    let f : LocallyConstant U ℂ :=
      ⟨fun x => form x 0, (d_openZeroForm_eq_zero_iff form).1 h⟩
    refine ⟨f, ?_⟩
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    rw [locallyConstantToZeroForm_apply]
    change form x 0 = form x v
    congr 1
    exact Subsingleton.elim _ _

/-- Locally constant sections and closed smooth zero-forms are canonically equivalent. -/
def locallyConstantClosedZeroFormEquiv (U : Opens E) :
    LocallyConstant U ℂ ≃ₗ[ℂ]
      LinearMap.ker (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) :=
  (LinearEquiv.ofInjective (locallyConstantToZeroForm U)
    (locallyConstantToZeroForm_injective U)).trans
      (LinearEquiv.ofEq _ _ (range_locallyConstantToZeroForm U))

@[simp]
theorem locallyConstantClosedZeroFormEquiv_coe (U : Opens E) (f : LocallyConstant U ℂ) :
    (locallyConstantClosedZeroFormEquiv U f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0) =
      locallyConstantToZeroForm U f := rfl

/-- Restriction of locally constant functions, with its pointwise complex-linear structure. -/
def locallyConstantRestrict {U V : Opens E} (h : V ≤ U) :
    LocallyConstant U ℂ →ₗ[ℂ] LocallyConstant V ℂ where
  toFun f := ⟨fun x => f ⟨x, h x.property⟩,
    f.isLocallyConstant.comp_continuous (continuous_subtype_val.subtype_mk _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual degree-zero inclusion commutes with restriction of open domains. -/
theorem restrict_locallyConstantToZeroForm {U V : Opens E} (h : V ≤ U)
    (f : LocallyConstant U ℂ) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h (locallyConstantToZeroForm U f) =
      locallyConstantToZeroForm V (locallyConstantRestrict h f) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply, locallyConstantToZeroForm_apply]
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms
