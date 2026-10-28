import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

/-! # Exponential Transport -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ExponentialTransport

noncomputable section

/-! Exponentials commute with continuous ring maps on convergent
series. A closed embedding reflects convergence, allowing source and
target algebras to use different local scalar fields. -/

open scoped Classical
open NormedSpace Set Filter _root_.Topology

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]

theorem map_exp_of_summable [T2Space B] (f : A →+* B) (hf : Continuous f) (x : A)
    (hx : Summable (fun m : ℕ => (m.factorial⁻¹ : ℚ) • x ^ m)) :
    f (exp x) = exp (f x) := by
  rw [exp_eq_tsum_rat, exp_eq_tsum_rat]
  refine ((hx.hasSum.map f hf).tsum_eq.symm).trans ?_
  apply tsum_congr
  intro m
  simp only [Function.comp_def, map_inv_natCast_smul f ℚ ℚ, map_pow]

omit [Algebra ℚ A] [Algebra ℚ B] [IsTopologicalRing A] [IsTopologicalRing B] in
theorem summable_of_closed_embedding
    {α : Type*} (f : A →+* B) (hf : IsClosedEmbedding f)
    (u : α → A) {b : B} (hu : HasSum (fun i => f (u i)) b) : Summable u := by
  have hb : b ∈ range f := by
    apply hf.isClosed_range.mem_of_tendsto hu
    apply Eventually.of_forall
    intro s
    exact ⟨∑ i ∈ s, u i, map_sum f u s⟩
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  apply hf.tendsto_nhds_iff.mpr
  rw [ha]
  simpa only [HasSum, Function.comp_def, map_sum] using hu

end

variable {K A B : Type*} [NontriviallyNormedField K] [CharZero K]
  [Ring A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]

omit [IsTopologicalRing A] in
theorem exp_series_summable_of_closed_embedding (f : A →+* B) (hf : IsClosedEmbedding f)
    (x : A) (hx : f x ∈ Metric.eball 0 (expSeries K B).radius) :
    Summable (fun m : ℕ => (m.factorial⁻¹ : ℚ) • x ^ m) := by
  have hs := expSeries_hasSum_exp_of_mem_ball' (f x) hx
  apply summable_of_closed_embedding f hf
  convert! hs using 1
  funext m
  simp only [map_inv_natCast_smul f ℚ K, map_pow]

theorem map_exp_of_closed_embedding (f : A →+* B) (hf : IsClosedEmbedding f)
    (x : A) (hx : f x ∈ Metric.eball 0 (expSeries K B).radius) :
    f (exp x) = exp (f x) := by
  let : Algebra ℚ B := RestrictScalars.algebra ℚ K B
  exact map_exp_of_summable f hf.continuous x (exp_series_summable_of_closed_embedding f hf x hx)

end

end OAI.NumberTheory.Quaternion.Arithmetic.ExponentialTransport
