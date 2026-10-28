import OAI.AlgebraicTopology.DeRham.Comparison.PartitionFormOperators
import OAI.Analysis.DifferentialForms.Manifold.OpenLocallyFiniteSum

/-! # Relative Partition Form Operators -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RelativePartitionFormOperators

noncomputable section

/-!
# Supported form operators relative to an arbitrary open domain

The scalar need only be smooth on the containing open set W. Its topological
support is measured inside W, so weights may accumulate at the boundary of W.
The extension to a smaller recipient open V is proved smooth locally there.
-/

open _root_.TopologicalSpace Function Filter Set
open scoped _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℕ} {U V W V' : Opens E}

omit [NormedSpace ℝ E] in
/-- Off its relative topological support, a weight vanishes on an ambient neighborhood. -/
theorem relativeWeight_eventually_zero (f : E → ℝ)
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (x : W) (hxU : (x : E) ∉ U) : f =ᶠ[𝓝 (x : E)] 0 := by
  have hnot : x ∉ tsupport (fun y : W => f y) := fun hx => hxU (hsupport hx)
  have hz : (fun y : W => f y) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  exact Analysis.DifferentialForms.Manifold.OpenLocallyFiniteSum.eventually_of_eventually_onOpen x hz

/-- Smoothness of supported zero extension only requires smoothness and support inside W. -/
theorem relativeSupportedFormExtension_smooth (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p) :
    ContDiffOn ℝ ∞ (fun x => f x • form.extension x) (V : Set E) := by
  intro x hxV
  by_cases hxU : x ∈ U
  · exact ((hf.contDiffAt (W.isOpen.mem_nhds (hVW hxV))).smul
      (form.smooth.contDiffAt ((U ⊓ V).isOpen.mem_nhds ⟨hxU, hxV⟩))).contDiffWithinAt
  · have hz := relativeWeight_eventually_zero f hsupport ⟨x, hVW hxV⟩ hxU
    have hprod : (fun y => f y • form.extension y) =ᶠ[𝓝 x]
        (fun _ => (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E p)) := by
      filter_upwards [hz] with y hy
      change f y = 0 at hy
      rw [hy]
      exact zero_smul ℝ (form.extension y)
    exact (contDiffAt_const.congr_of_eventuallyEq hprod).contDiffWithinAt

/-- Multiply on U∩V, then extend by zero to V using support relative to W. -/
def relativeSupportedFormExtension (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V p where
  toFun form := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw V (fun x => f x • form.extension x)
    (relativeSupportedFormExtension_smooth f hf hsupport hVW form)
  map_add' form other := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change f x • (form + other).extension x = f x • form.extension x + f x • other.extension x
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_add]
    exact smul_add _ _ _
  map_smul' z form := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change f x • (z • form).extension x = z • (f x • form.extension x)
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_smul]
    exact smul_comm (f x) z (form.extension x)

@[simp]
theorem relativeSupportedFormExtension_apply (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p) (x : V) :
    relativeSupportedFormExtension f hf hsupport hVW form x = f x • form.extension x := rfl

theorem relativeSupportedFormExtension_apply_of_mem (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p) (x : V) (hxU : (x : E) ∈ U) :
    relativeSupportedFormExtension f hf hsupport hVW form x =
      f x • form ⟨x, hxU, x.property⟩ := by
  rw [relativeSupportedFormExtension_apply]
  exact congrArg (fun z => f x • z) (form.extension_apply ⟨x, hxU, x.property⟩)

theorem relativeSupportedFormExtension_apply_of_notMem (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p) (x : V) (hxU : (x : E) ∉ U) :
    relativeSupportedFormExtension f hf hsupport hVW form x = 0 := by
  have hz : f x = 0 :=
    (relativeWeight_eventually_zero f hsupport ⟨(x : E), hVW x.property⟩ hxU).eq_of_nhds
  rw [relativeSupportedFormExtension_apply, hz]
  exact zero_smul ℝ (form.extension x)

/-- Relative extension respects restriction of the recipient open set. -/
theorem relativeSupportedFormExtension_restrict (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (hV'V : V' ≤ V) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U ⊓ V) p) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV'V (relativeSupportedFormExtension f hf hsupport hVW form) =
      relativeSupportedFormExtension f hf hsupport (hV'V.trans hVW)
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (inf_le_inf_left U hV'V) form) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  by_cases hxU : (x : E) ∈ U
  · rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply,
      relativeSupportedFormExtension_apply_of_mem f hf hsupport hVW form _ hxU,
      relativeSupportedFormExtension_apply_of_mem f hf hsupport _ _ _ hxU]
    rfl
  · rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply,
      relativeSupportedFormExtension_apply_of_notMem f hf hsupport hVW form _ hxU,
      relativeSupportedFormExtension_apply_of_notMem f hf hsupport _ _ _ hxU]

/-- For an already defined section on V, relative extension is multiplication by the weight. -/
theorem relativeSupportedFormExtension_restricted_apply (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (W : Set E))
    (hsupport : tsupport (fun x : W => f x) ⊆ {x : W | (x : E) ∈ U})
    (hVW : V ≤ W) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V p) (x : V) :
    relativeSupportedFormExtension f hf hsupport hVW
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form) x = f x • form x := by
  by_cases hxU : (x : E) ∈ U
  · exact relativeSupportedFormExtension_apply_of_mem f hf hsupport hVW _ x hxU
  · have hz : f x = 0 :=
      (relativeWeight_eventually_zero f hsupport ⟨(x : E), hVW x.property⟩ hxU).eq_of_nhds
    rw [relativeSupportedFormExtension_apply, hz]
    calc
      _ = (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) := zero_smul ℝ _
      _ = _ := (zero_smul ℝ _).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.RelativePartitionFormOperators
