import OAI.AlgebraicGeometry.Comparison.Betti.Pure.RadialHomotopy
import OAI.AlgebraicTopology.DeRham.Comparison.PoincareLocality
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothLocalExtension
import OAI.AlgebraicTopology.DeRham.Comparison.RadialSmoothPoincare
import OAI.Analysis.DifferentialForms.Manifold.OpenD

/-! # Local Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.LocalPoincare.Holomorphic

noncomputable section

/-!
# Local primitives of smooth differential forms

The genuine radial primitive of a closed pure holomorphic form is pure in
every degree. A smooth extension is used only along a ball where it equals
the original form; purity is established on exactly those radial segments.
-/

open Set Filter _root_.Metric _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.PoincareLocality

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {n : ℕ}

/-- A genuine global smooth representative agreeing with a closed open-domain
form on a ball gives a primitive on that ball. The representative is allowed
to have nonzero exterior derivative outside the ball. -/
theorem pure_local_poincare_of_ball_extension (U : Opens E) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0)
    (hpure : ∀ y : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form y)) (c : E) (r : ℝ) (hr : 0 < r)
    (hball : ball c r ⊆ (U : Set E)) (globalForm : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1))
    (hagree : ∀ y ∈ ball c r, globalForm y = form.extension y) :
    ∃ (V : Opens E) (hVU : V ≤ U), c ∈ V ∧
      ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n,
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hVU form ∧
        ∀ y : V, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (primitive y) := by
  have hglobalClosed : EqOn (extDeriv (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) 0 (ball c r) := by
    intro y hy
    have hlocal : (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) =ᶠ[𝓝 y] form.extension := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact hagree z hz
    have hzero : extDeriv form.extension y = 0 := by
      have h := congrArg (fun omega : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 2) => omega ⟨y, hball hy⟩) hclosed
      simpa only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply] using h
    exact hlocal.extDeriv_eq.trans hzero
  let shifted : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1) := Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate c globalForm
  have hshiftedClosed : EqOn (extDeriv (shifted : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) 0 (ball (0 : E) r) := by
    intro z hz
    change Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate c globalForm) z = 0
    rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_translate]
    change extDeriv (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) (c + z) = 0
    apply hglobalClosed
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  let primitiveGlobal : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n :=
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate (-c) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm shifted)
  let V : Opens E := ⟨ball c r, isOpen_ball⟩
  have hprimitivePure (y : V) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (primitiveGlobal (y : E)) := by
    apply RadialHomotopy.Holomorphic.pureCovector_radialHomotopy
    intro t ht
    have hy : -c + (y : E) ∈ ball (0 : E) r := by
      have hym : (y : E) ∈ ball c r := y.property
      simpa only [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero,
        add_zero, add_comm] using hym
    have hstar : StarConvex ℝ (0 : E) (ball (0 : E) r) :=
      (convex_ball (0 : E) r).starConvex (mem_ball_self hr)
    have htmem := hstar.smul_mem hy ht.1 ht.2
    have hc : c + t • (-c + (y : E)) ∈ ball c r := by
      simpa [Metric.mem_ball, dist_eq_norm] using htmem
    change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (globalForm (c + t • (-c + (y : E))))
    rw [hagree _ hc, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply form ⟨_, hball hc⟩]
    exact hpure _
  refine ⟨V, hball, mem_ball_self hr, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.onOpen V primitiveGlobal,
    ?_, hprimitivePure⟩
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  have hz : -c + (y : E) ∈ ball (0 : E) r := by
    have hy : (y : E) ∈ ball c r := y.property
    simpa only [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero, add_comm] using hy
  have hstar : StarConvex ℝ (0 : E) (ball (0 : E) r) :=
    (convex_ball (0 : E) r).starConvex (mem_ball_self hr)
  have hKzero := AlgebraicTopology.DeRham.Comparison.PoincareLocality.radialHomotopy_eq_zero_on_starConvex hstar hshiftedClosed hz
  have hK := AlgebraicTopology.DeRham.Comparison.RadialHomotopyIdentity.radialHomotopy_identity (shifted.smooth.of_le (by simp)) (-c + (y : E))
  rw [hKzero, add_zero] at hK
  have hprimitive : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d primitiveGlobal (y : E) = globalForm (y : E) := by
    change Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate (-c) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm shifted)) (y : E) = _
    rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_translate]
    change extDeriv (AlgebraicTopology.DeRham.Comparison.RadialOne.radialHomotopy (shifted : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) (-c + (y : E)) = _
    simpa [shifted, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate_apply, add_assoc] using hK
  change Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw V (primitiveGlobal : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) primitiveGlobal.smooth.contDiffOn) y =
    form ⟨(y : E), hball y.property⟩
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_ofRaw_apply]
  change Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d primitiveGlobal (y : E) = _
  rw [hprimitive]
  exact (hagree y y.property).trans (form.extension_apply ⟨(y : E), hball y.property⟩)

/-- Germ agreement with an actual global smooth form is enough to construct
a local primitive of a closed positive-degree form. -/
theorem pure_local_poincare_of_eventual_extension (U : Opens E)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0)
    (hpure : ∀ y : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form y))
    (x : U) (globalForm : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1))
    (hagree : (globalForm : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) =ᶠ[𝓝 (x : E)] form.extension) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n,
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hVU form ∧
        ∀ y : V, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (primitive y) := by
  have hnear : {y : E | y ∈ U ∧ globalForm y = form.extension y} ∈ 𝓝 (x : E) := by
    filter_upwards [U.isOpen.mem_nhds x.property, hagree] with y hy hgy
    exact ⟨hy, hgy⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  exact pure_local_poincare_of_ball_extension U form hclosed hpure x r hr
    (fun _ hy => (hball hy).1) globalForm (fun _ hy => (hball hy).2)

/-- Every closed positive-degree smooth form has a genuine smooth primitive
on a neighborhood of each point of its open domain. -/
theorem pure_local_poincare (U : Opens E) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0)
    (hpure : ∀ y : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form y)) (x : U) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n,
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hVU form ∧
        ∀ y : V, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (primitive y) := by
  obtain ⟨globalForm, hagree⟩ := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_global_smooth_extension form x
  exact pure_local_poincare_of_eventual_extension U form hclosed hpure x globalForm hagree

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.LocalPoincare.Holomorphic
