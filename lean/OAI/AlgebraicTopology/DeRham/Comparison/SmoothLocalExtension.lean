import OAI.Analysis.DifferentialForms.Manifold.OpenD
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Smooth Local Extension -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothLocalExtension

/-!
# Genuine smooth extensions of germs of open-domain differential forms

A compactly supported smooth bump which is identically one on a neighborhood
turns the actual zero extension into a globally smooth form. The plateau is
proved as an equality of germs, not merely an equality at the center.
-/

open Filter Set _root_.TopologicalSpace Function
open scoped _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-dimensional normed space has compactly supported smooth bumps
equal to one on a neighborhood, with support in any prescribed neighborhood.
The construction is the Euclidean bump used by mathlib's pointwise version,
with its stronger plateau property retained. -/
theorem exists_contDiff_bump_eventuallyEq_one [FiniteDimensional ℝ E]
    {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ rho : E → ℝ, ContDiff ℝ ∞ rho ∧ tsupport rho ⊆ s ∧
      HasCompactSupport rho ∧ rho =ᶠ[𝓝 x] (1 : E → ℝ) := by
  obtain ⟨d : ℝ, hd : 0 < d, hds : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.mp hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  let rho : E → ℝ := c ∘ toEuclidean
  have hsupport : Function.support rho ⊆ Euclidean.ball x d := by
    intro y hy
    have hcy : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using! hy
    rwa [c.support_eq] at hcy
  have htsupport : tsupport rho ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    exact closure_mono hsupport
  refine ⟨rho, ?_, htsupport.trans hds, ?_, ?_⟩
  · exact c.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  · exact Euclidean.isCompact_closedBall.of_isClosed_subset isClosed_closure htsupport
  · exact c.eventuallyEq_one.comp_tendsto (toEuclidean.continuous.tendsto x)

namespace SmoothOpenForm

variable {U : Opens E} {n : ℕ}

/-- Multiplying by a supported smooth scalar removes every boundary defect
of the zero extension. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.contDiff_supported_extension (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    ContDiff ℝ ∞ (fun x => rho x • form.extension x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hrho.contDiffAt.smul (form.smooth.contDiffAt (U.isOpen.mem_nhds hx))
  · have hnot : x ∉ tsupport rho := fun h => hx (hsupport h)
    have hzero : rho =ᶠ[𝓝 x] (0 : E → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    change rho y = 0 at hy
    rw [hy]
    exact zero_smul ℝ (form.extension y)

/-- A supported scalar produces a genuine globally smooth extension operator. -/
noncomputable def _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n →ₗ[ℂ] OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n where
  toFun form := OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (fun x => rho x • form.extension x)
    (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.contDiff_supported_extension rho hrho hsupport form)
  map_add' form otherForm := by
    apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
    intro x
    change rho x • (form + otherForm).extension x =
      rho x • form.extension x + rho x • otherForm.extension x
    rw [OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_add]
    exact smul_add _ _ _
  map_smul' c form := by
    apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
    intro x
    change rho x • (c • form).extension x = c • (rho x • form.extension x)
    rw [OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_smul]
    change rho x • (c • form.extension x) = c • (rho x • form.extension x)
    exact smul_comm (rho x) c (form.extension x)

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_apply (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (x : E) :
    OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form x = rho x • form.extension x := rfl

/-- Multiplication cannot enlarge the support beyond that of the cutoff. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_tsupport_subset (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hsupport : tsupport rho ⊆ U)
    (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    tsupport (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) ⊆
      tsupport rho :=
  tsupport_smul_subset_left rho form.extension

/-- Compact support of the cutoff passes to the resulting smooth form. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_hasCompactSupport (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hsupport : tsupport rho ⊆ U)
    (hcompact : HasCompactSupport rho) (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    HasCompactSupport (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) := by
  exact hcompact.of_isClosed_subset isClosed_closure
    (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_tsupport_subset rho hrho hsupport form)

/-- A plateau of the scalar gives agreement on a whole neighborhood. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_eventuallyEq (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupport : tsupport rho ⊆ U) (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) {x : E}
    (hone : rho =ᶠ[𝓝 x] (1 : E → ℝ)) :
    (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) =ᶠ[𝓝 x]
      form.extension := by
  filter_upwards [hone] with y hy
  change rho y = 1 at hy
  change rho y • form.extension y = form.extension y
  rw [hy, one_smul]

/-- Every germ of a genuine open-domain smooth form has a global smooth
representative in finite dimension. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_global_smooth_extension [FiniteDimensional ℝ E]
    (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (x : U) :
    ∃ globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n,
      (globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) =ᶠ[𝓝 (x : E)] form.extension := by
  obtain ⟨rho, hrho, hsupport, _, hone⟩ :=
    exists_contDiff_bump_eventuallyEq_one (U.isOpen.mem_nhds x.property)
  exact ⟨OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form,
    OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_eventuallyEq rho hrho hsupport form hone⟩

/-- The global representative can furthermore be chosen compactly supported
inside the original open domain. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_compactly_supported_global_smooth_extension [FiniteDimensional ℝ E]
    (form : OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (x : U) :
    ∃ globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n,
      HasCompactSupport (globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) ∧
      tsupport (globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) ⊆ U ∧
      (globalForm : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) =ᶠ[𝓝 (x : E)] form.extension := by
  obtain ⟨rho, hrho, hsupport, hcompact, hone⟩ :=
    exists_contDiff_bump_eventuallyEq_one (U.isOpen.mem_nhds x.property)
  refine ⟨OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension rho hrho hsupport form,
    OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_hasCompactSupport rho hrho hsupport hcompact form,
    (OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_tsupport_subset rho hrho hsupport form).trans hsupport, ?_⟩
  exact OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.supportedGlobalExtension_eventuallyEq rho hrho hsupport form hone

end SmoothOpenForm

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothLocalExtension
