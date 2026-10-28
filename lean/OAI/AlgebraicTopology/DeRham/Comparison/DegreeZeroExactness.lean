import OAI.Analysis.DifferentialForms.Manifold.DegreeZero
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Degree Zero Exactness -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DegreeZeroExactness

noncomputable section

/-!
# Degree-zero local exactness for actual differential forms

On an open subset of a real normed space, a differentiable complex-valued
function has zero derivative exactly when its restriction is locally constant.
The bundled exterior derivative has the same kernel under the actual
identification of smooth functions with zero-forms.
-/

open scoped ContDiff _root_.Topology
open Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A locally constant restriction on an open set determines a constant germ
in the ambient normed space. -/
theorem eventually_eq_const_of_isLocallyConstant_on_open {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : IsLocallyConstant (fun x : U => f x)) {x : E} (hx : x ∈ U) :
    f =ᶠ[𝓝 x] (fun _ : E => f x) := by
  obtain ⟨V, hV, hxV, hconst⟩ := hf.exists_open (⟨x, hx⟩ : U)
  have himage : IsOpen ((Subtype.val : U → E) '' V) :=
    hU.isOpenMap_subtype_val V hV
  have hximage : x ∈ (Subtype.val : U → E) '' V := ⟨⟨x, hx⟩, hxV, rfl⟩
  filter_upwards [himage.mem_nhds hximage] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hconst z hz

/-- Locally constant functions on an open set are smooth on that set. -/
theorem contDiffOn_of_isLocallyConstant_on_open {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : IsLocallyConstant (fun x : U => f x)) :
    ContDiffOn ℝ ∞ f U := by
  intro x hx
  exact (contDiffAt_const.congr_of_eventuallyEq
    (eventually_eq_const_of_isLocallyConstant_on_open hU hf hx)).contDiffWithinAt

/-- A locally constant restriction to an open set has zero ambient derivative there.
No differentiability assumption is needed in this direction. -/
theorem fderiv_eq_zero_of_isLocallyConstant_on_open {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : IsLocallyConstant (fun x : U => f x)) {x : E} (hx : x ∈ U) :
    fderiv ℝ f x = 0 := by
  have heq := eventually_eq_const_of_isLocallyConstant_on_open hU hf hx
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

/-- The kernel of the derivative on an open domain is exactly the locally
constant functions. The function need only be differentiable on that domain. -/
theorem fderiv_eq_zero_on_open_iff {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : DifferentiableOn ℝ f U) :
    (∀ x ∈ U, fderiv ℝ f x = 0) ↔ IsLocallyConstant (fun x : U => f x) := by
  constructor
  · intro h t
    have hopen : IsOpen (U ∩ f ⁻¹' t) :=
      hU.isOpen_inter_preimage_of_fderiv_eq_zero hf (fun x hx => h x hx) t
    have hpre := hopen.preimage (continuous_subtype_val : Continuous (Subtype.val : U → E))
    convert hpre using 1
    ext x
    simp
  · intro h x hx
    exact fderiv_eq_zero_of_isLocallyConstant_on_open hU h hx

/-- The actual derivative of a bundled zero-form vanishes on an open set exactly
when its smooth function is locally constant there. -/
theorem d_toZeroForm_eq_zero_on_open_iff (f : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E)
    {U : Set E} (hU : IsOpen U) :
    (∀ x ∈ U, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d f.toZeroForm x = 0) ↔
      IsLocallyConstant (fun x : U => f x) := by
  rw [← fderiv_eq_zero_on_open_iff hU
    ((f.smooth.differentiable (by simp)).differentiableOn)]
  constructor
  · intro h x hx
    apply ContinuousLinearMap.ext
    intro v
    have heval := congrArg (fun a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 => a (fun _ => v)) (h x hx)
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply, zero_apply] using heval
  · intro h x hx
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, h x hx,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, zero_apply]

/-- On the entire normed space the degree-zero exterior kernel consists of the
locally constant smooth functions. -/
theorem d_toZeroForm_eq_zero_iff (f : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction E) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d f.toZeroForm = 0 ↔ IsLocallyConstant (f : E → ℂ) := by
  constructor
  · intro h
    apply isLocallyConstant_of_fderiv_eq_zero (f.smooth.differentiable (by simp))
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have heval := congrArg (fun a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 1 => a x (fun _ => v)) h
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, zero_apply] using heval
  · intro h
    apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    have heq : (f : E → ℂ) =ᶠ[𝓝 x] (fun _ : E => f x) := h.eventually_eq x
    simp only [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, heq.fderiv_eq, fderiv_const_apply,
      zero_apply, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The degree-zero kernel statement applies directly to a smooth zero-form. -/
theorem d_zeroForm_eq_zero_iff (form : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form = 0 ↔ IsLocallyConstant (form.toSmoothFunction : E → ℂ) := by
  simpa only [OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.toZeroForm_toSmoothFunction] using
    d_toZeroForm_eq_zero_iff form.toSmoothFunction

end

end OAI.AlgebraicTopology.DeRham.Comparison.DegreeZeroExactness
