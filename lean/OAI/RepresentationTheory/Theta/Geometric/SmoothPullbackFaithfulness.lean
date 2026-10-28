import OAI.Analysis.DifferentialForms.Manifold.ManifoldPullback
import OAI.Analysis.DifferentialForms.Manifold.TangentCoordinates

/-! # Smooth Pullback Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothPullbackFaithfulness

noncomputable section

/-! Surjective maps with surjective tangent maps faithfully pull back actual
smooth forms. Preferred chart covectors also determine the original form. -/

open scoped _root_.Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

theorem smoothFormPullback_injective (g : M → N)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (hs : Function.Surjective g)
    (hd : ∀ x, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x)) (n : ℕ) :
    Function.Injective (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (n := n) g hg) := by
  intro form other h
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro y
  obtain ⟨x, rfl⟩ := hs y
  ext v
  choose w hw using fun i => hd x (v i)
  have he := congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n => a x w) h
  change form (g x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (w i)) =
    other (g x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (w i)) at he
  simpa only [hw] using he

omit [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem smoothOneForm_eq_of_preferredChart (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (h : ∀ x u, form.val.inChart (chartAt E x) (chartAt E x x) (fun _ => u) =
      other.val.inChart (chartAt E x) (chartAt E x x) (fun _ => u)) : form = other := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  let e := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)
  have he := h x (e (v 0))
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ _ (chart_mem_atlas E x) x (mem_chart_source E x),
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ _ (chart_mem_atlas E x) x (mem_chart_source E x)] at he
  have hv : (fun _ : Fin 1 => e.symm (e (v 0))) = v := by
    funext i
    rw [e.symm_apply_apply]
    exact congrArg v (Subsingleton.elim 0 i)
  change form x (fun _ : Fin 1 => e.symm (e (v 0))) =
    other x (fun _ : Fin 1 => e.symm (e (v 0))) at he
  simpa only [hv] using he

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothPullbackFaithfulness
