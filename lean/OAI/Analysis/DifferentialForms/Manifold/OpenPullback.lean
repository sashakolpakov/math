import OAI.Analysis.DifferentialForms.Manifold.OpenD
import OAI.Analysis.DifferentialForms.Manifold.Vectors

/-! # Open Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-!
# Pullback of differential forms on open domains

The map need only be smooth on its source domain. Its derivative acts on each
tangent argument, and the value of the form is taken in the target domain.
Zero extensions serve only to construct representatives; the resulting pullback
is local, respects restrictions, and commutes with exterior differentiation.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Opens E} {V : Opens F} {W : Opens G} {n : ℕ}

/-- Pullback by a map smooth on an open source and taking values in an open
target, complex-linear in the differential form. -/
noncomputable def OpenD.SmoothOpenForm.pullback (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F)) :
    OpenD.SmoothOpenForm V n →ₗ[ℂ] OpenD.SmoothOpenForm U n where
  toFun form := OpenD.SmoothOpenForm.ofRaw U
    (fun x => (form.extension (f x)).compContinuousLinearMap (fderiv ℝ f x))
    (Alternatization.contDiffOn_alternating_compContinuousLinearMap
      (form.smooth.comp hf hUV) (hf.fderiv_of_isOpen U.isOpen (by simp)))
  map_add' form otherForm := by
    apply OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change (form + otherForm).extension (f x) (fun i => fderiv ℝ f x (v i)) =
      form.extension (f x) (fun i => fderiv ℝ f x (v i)) +
        otherForm.extension (f x) (fun i => fderiv ℝ f x (v i))
    rw [OpenD.SmoothOpenForm.extension_add]
    rfl
  map_smul' c form := by
    apply OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change (c • form).extension (f x) (fun i => fderiv ℝ f x (v i)) =
      c • form.extension (f x) (fun i => fderiv ℝ f x (v i))
    rw [OpenD.SmoothOpenForm.extension_smul]
    rfl

/-- The pullback at a source point only uses the value in the target domain. -/
@[simp] theorem OpenD.SmoothOpenForm.pullback_apply (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F)) (form : OpenD.SmoothOpenForm V n) (x : U) :
    OpenD.SmoothOpenForm.pullback f hf hUV form x =
      (form ⟨f x, hUV x.property⟩).compContinuousLinearMap (fderiv ℝ f x) := by
  change (form.extension (f x)).compContinuousLinearMap (fderiv ℝ f x) = _
  exact congrArg (fun value : Basic.FormValue F n =>
    value.compContinuousLinearMap (fderiv ℝ f x))
      (OpenD.SmoothOpenForm.extension_apply form ⟨f x, hUV x.property⟩)

theorem OpenD.SmoothOpenForm.pullback_apply_vectors (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F)) (form : OpenD.SmoothOpenForm V n)
    (x : U) (v : Fin n → E) :
    OpenD.SmoothOpenForm.pullback f hf hUV form x v =
      form ⟨f x, hUV x.property⟩ (fun i => fderiv ℝ f x (v i)) := by
  rw [OpenD.SmoothOpenForm.pullback_apply]
  rfl

/-- The identity map acts as the identity on forms. -/
@[simp] theorem OpenD.SmoothOpenForm.pullback_id (form : OpenD.SmoothOpenForm U n) :
    OpenD.SmoothOpenForm.pullback (id : E → E) contDiffOn_id (mapsTo_id (U : Set E)) form = form := by
  ext x v
  simp [OpenD.SmoothOpenForm.pullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Pullback is contravariantly compatible with composition on open domains. -/
theorem OpenD.SmoothOpenForm.pullback_comp (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F))
    (g : F → G) (hg : ContDiffOn ℝ ∞ g (V : Set F))
    (hVW : MapsTo g (V : Set F) (W : Set G)) (form : OpenD.SmoothOpenForm W n) :
    OpenD.SmoothOpenForm.pullback (g ∘ f) (hg.comp hf hUV) (hVW.comp hUV) form =
      OpenD.SmoothOpenForm.pullback f hf hUV (OpenD.SmoothOpenForm.pullback g hg hVW form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [OpenD.SmoothOpenForm.pullback_apply_vectors, Function.comp_apply]
  rw [fderiv_comp (x : E)
    ((hg.contDiffAt (V.isOpen.mem_nhds (hUV x.property))).differentiableAt (by simp))
    ((hf.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))]
  rfl

/-- Exterior differentiation commutes with pullback; no smoothness outside the
open source domain is required. -/
theorem OpenD.SmoothOpenForm.d_pullback (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F)) (form : OpenD.SmoothOpenForm V n) :
    OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.pullback f hf hUV form) = OpenD.SmoothOpenForm.pullback f hf hUV (OpenD.SmoothOpenForm.d form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [OpenD.SmoothOpenForm.pullback_apply, OpenD.SmoothOpenForm.d_apply]
  change OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.ofRaw U _ _) x =
    (extDeriv form.extension (f x)).compContinuousLinearMap (fderiv ℝ f x)
  rw [OpenD.SmoothOpenForm.d_ofRaw_apply]
  exact extDeriv_pullback
    ((form.smooth.contDiffAt (V.isOpen.mem_nhds (hUV x.property))).differentiableAt
      (by simp))
    (hf.contDiffAt (U.isOpen.mem_nhds x.property)) SquareZero.minSmoothness_real_two_le_infty

/-- Restricting the source commutes with pullback. -/
theorem OpenD.SmoothOpenForm.restrict_pullback {U' : Opens E} (h : U' ≤ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV : MapsTo f (U : Set E) (V : Set F)) (form : OpenD.SmoothOpenForm V n) :
    OpenD.SmoothOpenForm.restrict h (OpenD.SmoothOpenForm.pullback f hf hUV form) =
      OpenD.SmoothOpenForm.pullback f (hf.mono h) (hUV.mono_left h) form := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rfl

/-- Restricting the target form does not change its pullback when the map takes
values in the smaller target. -/
theorem OpenD.SmoothOpenForm.pullback_restrict {V' : Opens F} (h : V' ≤ V)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hUV' : MapsTo f (U : Set E) (V' : Set F)) (form : OpenD.SmoothOpenForm V n) :
    OpenD.SmoothOpenForm.pullback f hf hUV' (OpenD.SmoothOpenForm.restrict h form) =
      OpenD.SmoothOpenForm.pullback f hf (hUV'.mono_right h) form := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [OpenD.SmoothOpenForm.pullback_apply, OpenD.SmoothOpenForm.pullback_apply]
  rfl

/-- The pullback along an open inclusion is the usual restriction of a form. -/
@[simp] theorem OpenD.SmoothOpenForm.pullback_inclusion {U' : Opens E} (h : U' ≤ U)
    (form : OpenD.SmoothOpenForm U n) :
    OpenD.SmoothOpenForm.pullback (id : E → E) contDiffOn_id h form = OpenD.SmoothOpenForm.restrict h form := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [OpenD.SmoothOpenForm.pullback_apply (U := U') (V := U) (id : E → E) contDiffOn_id h form x]
  ext v
  simp

/-- Changing an ambient representative of a map away from the open source
does not change the pullback. -/
theorem OpenD.SmoothOpenForm.pullback_congr {f g : E → F} (hf : ContDiffOn ℝ ∞ f (U : Set E))
    (hg : ContDiffOn ℝ ∞ g (U : Set E))
    (hfUV : MapsTo f (U : Set E) (V : Set F))
    (hgUV : MapsTo g (U : Set E) (V : Set F))
    (hfg : EqOn f g (U : Set E)) (form : OpenD.SmoothOpenForm V n) :
    OpenD.SmoothOpenForm.pullback f hf hfUV form = OpenD.SmoothOpenForm.pullback g hg hgUV form := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  have heq : f =ᶠ[𝓝 (x : E)] g := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact hfg hy
  change (form.extension (f x)).compContinuousLinearMap (fderiv ℝ f x) =
    (form.extension (g x)).compContinuousLinearMap (fderiv ℝ g x)
  rw [hfg x.property, heq.fderiv_eq]

/-- The open-domain and global pullback constructions agree on their common
domain of definition. -/
theorem OpenD.SmoothOpenForm.pullback_onOpen (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hUV : MapsTo f (U : Set E) (V : Set F)) (form : Basic.SmoothForm F n) :
    OpenD.SmoothOpenForm.pullback f hf.contDiffOn hUV (Basic.SmoothForm.onOpen V form) =
      Basic.SmoothForm.onOpen U (Basic.SmoothForm.pullback f hf form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  rw [OpenD.SmoothOpenForm.pullback_apply]
  rfl

end OAI.Analysis.DifferentialForms.Manifold
