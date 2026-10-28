import OAI.Analysis.HodgeTheory.Decomposition.WeightedPlancherel

/-! # Fourier Moment -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FourierMoment.Constructions

noncomputable section

/-! Integrability of the first-order Fourier moment for actual vector-valued
Schwartz functions. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem schwartz_normsq_moment_integrable (f : 𝓢(E, F)) :
    Integrable (fun x => ‖x‖ ^ 2 * ‖f x‖ ^ 2) volume := by
  let g := SchwartzMap.smulLeftCLM F (fun x : E => ‖x‖ ^ 2) f
  have hi := Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable g f)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro x
  change (inner ℂ (g x) (f x)).re = ‖x‖ ^ 2 * ‖f x‖ ^ 2
  rw [show g x = ‖x‖ ^ 2 • f x from
    congrFun (SchwartzMap.smulLeftCLM_apply (Function.hasTemperateGrowth_norm_sq E) f) x]
  calc
    _ = (‖x‖ ^ 2 • inner ℂ (f x) (f x)).re :=
      congrArg Complex.re (inner_smul_real_left (𝕜 := ℂ) (f x) (f x) (‖x‖ ^ 2))
    _ = ‖x‖ ^ 2 * RCLike.re (inner ℂ (f x) (f x)) :=
      Complex.reCLM.map_smul (‖x‖ ^ 2) (inner ℂ (f x) (f x))
    _ = _ := congrArg (fun r : ℝ => ‖x‖ ^ 2 * r) (inner_self_eq_norm_sq (𝕜 := ℂ) (f x))

end

end OAI.Analysis.HodgeTheory.Decomposition.FourierMoment.Constructions
