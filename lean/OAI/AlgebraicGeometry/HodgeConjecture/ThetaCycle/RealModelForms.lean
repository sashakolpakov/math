import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelCharts
import OAI.Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph

/-! # Real Model Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelForms.CM

noncomputable section

/-! ThetaCycle: actual differential forms and closed forms transported through
the identity diffeomorphism to real model coordinates. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open Set Filter

universe u v

variable {E F : Type u} {M : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def linearRechartForms (e : E ≃L[ℝ] F) (n : ℕ) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F M n := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.diffeomorphPullback (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞) n).symm

def linearRechartClosedForms (e : E ≃L[ℝ] F) (n : ℕ) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms F M n := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  exact (Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldClosedFormsDiffeomorph (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞) n).symm

theorem linear_rechart_forms_d (e : E ≃L[ℝ] F) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (linearRechartForms e n form) =
      linearRechartForms e (n + 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback
    (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞).symm
    (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞).symm.contMDiff form

theorem linear_rechart_closed_forms_val (e : E ≃L[ℝ] F) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (linearRechartClosedForms e n form).val = linearRechartForms e n form.val := rfl

theorem linear_rechart_forms_in_chart (e : E ≃L[ℝ] F) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (a : OpenPartialHomeomorph M E)
    (ha : a ∈ atlas E M) (y : F)
    (hy : e.symm y ∈ a.target) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (linearRechartForms e n form).val.inChart
        (a.trans e.toHomeomorph.toOpenPartialHomeomorph) y =
      (form.val.inChart a (e.symm y)).compContinuousLinearMap e.symm.toContinuousLinearMap := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  let c := a.trans e.toHomeomorph.toOpenPartialHomeomorph
  let g := (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞).symm
  have hc : c ∈ atlas F M := ⟨a, ha, rfl⟩
  have hyc : y ∈ c.target := by
    simpa only [c, mfld_simps] using! hy
  have hs : g (c.symm y) ∈ a.source := by
    simpa only [g, RealModelCharts.CM.linearRechartDiffeomorph, c, mfld_simps] using! a.map_target hy
  have heq : (a ∘ g ∘ c.symm) =ᶠ[𝓝 y] e.symm := by
    filter_upwards [c.open_target.mem_nhds hyc] with z hz
    have ht : e.symm z ∈ a.target := by
      simpa only [c, mfld_simps] using! hz
    simpa only [g, RealModelCharts.CM.linearRechartDiffeomorph, c, Function.comp_def, mfld_simps] using!
      a.right_inv ht
  have hd : fderiv ℝ (a ∘ g ∘ c.symm) y = e.symm.toContinuousLinearMap :=
    heq.fderiv_eq.trans e.symm.fderiv
  have h := form.val.pullback_inChart g c a hc ha hyc hs
    (g.contMDiff.mdifferentiableAt (by simp))
  rw [hd] at h
  have hv : a (g (c.symm y)) = e.symm y := heq.eq_of_nhds
  rw [hv] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelForms.CM
