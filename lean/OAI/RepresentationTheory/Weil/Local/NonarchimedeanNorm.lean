import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Nonarchimedean Norm -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm.Construction

noncomputable section

/-! A nondiscrete nonarchimedean field topology forces its multiplicative norm to be ultrametric. -/

open scoped _root_.Topology

theorem nonarchimedean_norm_ultrametric
    (k : Type) [NormedField k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) : IsUltrametricDist k := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hNondiscrete hd).elim
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    (Metric.ball (0 : k) 1) (Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds U.zero_mem)
  obtain ⟨u, hu, huε⟩ := NormedField.exists_norm_lt k hε
  have huU : u ∈ U := hεU (by simpa using huε)
  apply isUltrametricDist_iff_forall_norm_natCast_le_one.mpr
  intro n
  by_contra! hn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ‖u‖) hn
  have hbound := hU (U.nsmul_mem huU (n ^ m))
  rw [Metric.mem_ball, dist_zero_right, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow] at hbound
  exact lt_asymm ((div_lt_iff₀ hu).mp hm) hbound

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm.Construction
