import OAI.AlgebraicTopology.DeRham.Comparison.CompactFormExtension
import OAI.AlgebraicTopology.DeRham.Comparison.RadialLocalization
import OAI.AlgebraicTopology.DeRham.Comparison.RadialSmoothPoincare

/-! # Radial Open Poincare -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialOpenPoincare

noncomputable section

/-!
# The radial homotopy on an open star-shaped domain

One fixed radial integral of the domain's actual form is used everywhere.
Smooth extensions near compact radial segments prove its local smoothness
and derivative identity without imposing any boundary regularity.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem isCompact_radialSegment (x : E) : IsCompact (segment ℝ (0 : E) x) := by
  rw [segment_eq_image]
  simpa only [Pi.smul_def', id_eq, smul_zero, zero_add] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).image
      (continuous_id.smul continuous_const : Continuous (fun t : ℝ => t • x))

variable [FiniteDimensional ℝ E] {U : Opens E} {n : ℕ}

/-- The actual radial integral of an open-domain smooth form is smooth at
every point of a star-shaped domain. -/
theorem contDiffAt_radialHomotopy_extension
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    {x : E} (hx : x ∈ U) : ContDiffAt ℝ ∞ (RadialOne.radialHomotopy form.extension) x := by
  obtain ⟨globalForm, hagree⟩ := CompactFormExtension.exists_smoothForm_extension_nhdsSet form
    (isCompact_radialSegment x) (hstar.segment_subset hx)
  have hK := RadialLocalization.radialHomotopy_eventuallyEq_of_nhdsSegment hagree
  exact (RadialHomotopySmooth.contDiff_radialHomotopy globalForm.smooth).contDiffAt.congr_of_eventuallyEq hK.symm

/-- Smoothness on the whole open star-shaped domain follows from the
compact-segment localization at every point. -/
theorem contDiffOn_radialHomotopy_extension
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) :
    ContDiffOn ℝ ∞ (RadialOne.radialHomotopy form.extension) (U : Set E) := by
  intro x hx
  exact (contDiffAt_radialHomotopy_extension hstar form hx).contDiffWithinAt

/-- The full radial identity holds for the actual extension of an open-domain
form at every point inside a star-shaped domain. -/
theorem radialHomotopy_extension_identity
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    {x : E} (hx : x ∈ U) :
    extDeriv (RadialOne.radialHomotopy form.extension) x +
      RadialOne.radialHomotopy (extDeriv form.extension) x = form.extension x := by
  obtain ⟨globalForm, hagree⟩ := CompactFormExtension.exists_smoothForm_extension_nhdsSet form
    (isCompact_radialSegment x) (hstar.segment_subset hx)
  have hK := RadialLocalization.radialHomotopy_eventuallyEq_of_nhdsSegment hagree
  have hdK := hK.extDeriv_eq
  have hKd : RadialOne.radialHomotopy (extDeriv (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) x =
      RadialOne.radialHomotopy (extDeriv form.extension) x := by
    apply RadialLocalization.radialHomotopy_congr_segment
    intro t ht
    have hmem : t • x ∈ segment ℝ (0 : E) x := by
      rw [segment_eq_image]
      exact ⟨t, ht, by simp⟩
    exact (hagree.filter_mono (nhds_le_nhdsSet hmem)).extDeriv_eq
  have hxmem : x ∈ segment ℝ (0 : E) x := right_mem_segment ℝ (0 : E) x
  have hvalue := (hagree.filter_mono (nhds_le_nhdsSet hxmem)).eq_of_nhds
  have h := RadialHomotopyIdentity.radialHomotopy_identity (globalForm.smooth.of_le (by simp)) x
  rwa [hdK, hKd, hvalue] at h

omit [FiniteDimensional ℝ E] in
/-- Radial integration only visits the domain, where the derivative of the
domain form agrees with the derivative of its auxiliary extension. -/
theorem radialHomotopy_extension_d_eq
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    {x : E} (hx : x ∈ U) :
    RadialOne.radialHomotopy (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form).extension x =
      RadialOne.radialHomotopy (extDeriv form.extension) x := by
  apply RadialLocalization.radialHomotopy_congr_segment
  intro t ht
  exact Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form)
    ⟨t • x, hstar.smul_mem hx ht.1 ht.2⟩

end

namespace SmoothOpenForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {U : Opens E} {n : ℕ}

/-- The standard radial homotopy as an actual smooth form on a star-shaped
open domain. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm (hstar : StarConvex ℝ (0 : E) (U : Set E))
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U (RadialOne.radialHomotopy form.extension)
    (contDiffOn_radialHomotopy_extension hstar form)

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm_apply (hstar : StarConvex ℝ (0 : E) (U : Set E))
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (x : U) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar form x = RadialOne.radialHomotopy form.extension x := rfl

/-- The full homotopy identity for open-domain smooth forms. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_radialHomotopy_add_radialHomotopy_d
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar form) + Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form) = form := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.add_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_ofRaw_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw_apply]
  rw [radialHomotopy_extension_d_eq hstar form x.property]
  exact (radialHomotopy_extension_identity hstar form x.property).trans
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply form x)

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm_zero (hstar : StarConvex ℝ (0 : E) (U : Set E)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar (0 : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) = 0 := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  simp [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension, Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_zero]

/-- Every closed positive-degree smooth form on an open star-shaped domain
has a smooth primitive on that entire domain. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex_zero
    (hstar : StarConvex ℝ (0 : E) (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0) : ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = form := by
  refine ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar form, ?_⟩
  have h := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_radialHomotopy_add_radialHomotopy_d hstar form
  simpa only [hclosed, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm_zero, add_zero] using h

end SmoothOpenForm

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialOpenPoincare
