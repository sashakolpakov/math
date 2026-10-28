import OAI.AlgebraicTopology.DeRham.Comparison.RadialOpenPoincare
import OAI.Analysis.DifferentialForms.Manifold.OpenPullback

/-! # Star Convex Poincare -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.StarConvexPoincare.SmoothOpenForm

noncomputable section

/-!
# Global Poincare lemma on open star-convex and convex domains

Translation moves the arbitrary center to the origin. The primitive then
comes from the checked radial integral on the entire translated open set.
-/

open Set _root_.TopologicalSpace
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {U : Opens E} {n : ℕ}

/-- Every closed positive-degree form on an open domain star-convex about
any center has a smooth primitive on that entire domain. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex {c : E}
    (hstar : StarConvex ℝ c (U : Set E)) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0) : ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = form := by
  let V : Opens E := ⟨(fun z : E => c + z) ⁻¹' (U : Set E),
    U.isOpen.preimage (continuous_const.add continuous_id)⟩
  have hstarV : StarConvex ℝ (0 : E) (V : Set E) := by
    change StarConvex ℝ (0 : E) ((fun z : E => c + z) ⁻¹' (U : Set E))
    apply StarConvex.preimage_add_right
    simpa using hstar
  have hplus : MapsTo (fun z : E => c + z) (V : Set E) (U : Set E) :=
    fun _ hz => hz
  have hminus : MapsTo (fun z : E => -c + z) (U : Set E) (V : Set E) := by
    intro z hz
    change c + (-c + z) ∈ U
    simpa [add_assoc] using hz
  have hsplus : ContDiffOn ℝ ∞ (fun z : E => c + z) (V : Set E) :=
    (contDiff_const.add contDiff_id).contDiffOn
  have hsminus : ContDiffOn ℝ ∞ (fun z : E => -c + z) (U : Set E) :=
    (contDiff_const.add contDiff_id).contDiffOn
  let shifted : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V (n + 1) := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback (fun z : E => c + z) hsplus hplus form
  have hshifted : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d shifted = 0 := by
    dsimp only [shifted]
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_pullback, hclosed, map_zero]
  obtain ⟨primitive, hprimitive⟩ := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex_zero hstarV shifted hshifted
  refine ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback (fun z : E => -c + z) hsminus hminus primitive, ?_⟩
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_pullback, hprimitive]
  dsimp only [shifted]
  rw [← Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_comp]
  calc
    _ = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback (id : E → E) contDiffOn_id (mapsTo_id (U : Set E)) form := by
      apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_congr
      intro z _
      simp
    _ = form := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_id form

/-- Every closed positive-degree smooth form on an open convex domain is
globally exact, including the empty-domain case. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_convex (hconvex : Convex ℝ (U : Set E))
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0) :
    ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = form := by
  by_cases hU : (U : Set E).Nonempty
  · obtain ⟨c, hc⟩ := hU
    exact Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex (hconvex.starConvex hc) form hclosed
  · apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex_zero (form := form) ?_ hclosed
    intro z hz
    exact (hU ⟨z, hz⟩).elim

end

end OAI.AlgebraicTopology.DeRham.Comparison.StarConvexPoincare.SmoothOpenForm
