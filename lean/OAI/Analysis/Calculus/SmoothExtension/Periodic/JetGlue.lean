import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sublevel

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Gluing values on an open set also glues every actual iterated
derivative there, without imposing additional derivative compatibility. -/
theorem iteratedFDeriv_eqOn_of_eqOn_open {Ω : Set E} (hΩ : IsOpen Ω)
    {f g : E → F} (he : EqOn f g Ω) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ j g) Ω := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] g := eventually_of_mem (hΩ.mem_nhds hx) (fun y hy ↦ he hy)
  exact (hev.iteratedFDeriv ℝ j).self_of_nhds

/-- For continuous jets, compatibility extends to the closed boundary.
Thus the global extension preserves the jets of each local representative. -/
theorem iteratedFDeriv_eqOn_closure_of_eqOn_open {Ω : Set E} (hΩ : IsOpen Ω)
    {f g : E → F} {q j : ℕ} (hf : ContDiff ℝ q f) (hg : ContDiff ℝ q g)
    (hj : j ≤ q) (he : EqOn f g Ω) :
    EqOn (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ j g) (closure Ω) := by
  have hfc : Continuous (iteratedFDeriv ℝ j f) := hf.continuous_iteratedFDeriv (by exact_mod_cast hj)
  have hgc : Continuous (iteratedFDeriv ℝ j g) := hg.continuous_iteratedFDeriv (by exact_mod_cast hj)
  have hclosed : IsClosed {x | iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x} :=
    isClosed_eq hfc hgc
  exact closure_minimal (iteratedFDeriv_eqOn_of_eqOn_open hΩ he j) hclosed

end OAI.Analysis.Calculus.SmoothExtension
