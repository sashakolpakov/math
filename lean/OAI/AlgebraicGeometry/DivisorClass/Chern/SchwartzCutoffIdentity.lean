import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint

/-! # Schwartz Cutoff Identity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCutoffIdentity

noncomputable section

section

/-! Exact additivity of real L² pairings with genuine vector-valued Schwartz tests. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem schwartzLp_inner_add {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a : Lp F 2 (volume : Measure E)) (p q : 𝓢(E, F)) :
    inner ℝ a ((p + q).toLp 2 volume) = inner ℝ a (p.toLp 2 volume) + inner ℝ a (q.toLp 2 volume) :=
  (congrArg (fun v : Lp F 2 (volume : Measure E) => inner ℝ a v)
    ((SchwartzMap.toLpCLM ℝ F 2 volume).map_add p q)).trans (inner_add_right a _ _)

theorem real_interleave_pair_blocks (p c b d : ℝ) : (p + c) + (b + d) = p + b + c + d := by ring

end

/-! A scalar cutoff equal to one on a Schwartz field's support fixes that exact field. -/

open scoped SchwartzMap

theorem schwartz_cutoff_eq_of_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : 𝓢(E, ℂ)) (q : 𝓢(E, F)) (hg : ∀ x ∈ tsupport q, g x = 1) :
    SchwartzMap.smulLeftCLM F g q = q := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
  by_cases hx : q x = 0
  · rw [hx, smul_zero]
  · rw [hg x (subset_tsupport q hx), one_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCutoffIdentity
