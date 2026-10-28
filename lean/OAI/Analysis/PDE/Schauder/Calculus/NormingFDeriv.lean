import OAI.Analysis.PDE.Schauder.Calculus.PointwiseDerivative

open Set Filter Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Schauder

/-- A norming family detects an actual Frechet derivative when the proposed
operator derivative is norm-continuous. The parameter space is arbitrary. -/
theorem hasFDerivAt_of_norming_family
    {Z F G I : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : I → F →L[ℝ] G) (hL : ∀ i, ‖L i‖ ≤ 1)
    (hnorm : ∀ (v : F) (C : ℝ), 0 ≤ C → (∀ i, ‖L i v‖ ≤ C) → ‖v‖ ≤ C)
    {f : Z → F} {g : Z → Z →L[ℝ] F} {U : Set Z} (hU : IsOpen U) {a : Z} (ha : a ∈ U)
    (hg : ContinuousAt g a)
    (hd : ∀ t ∈ U, ∀ i, HasFDerivAt (fun s => L i (f s)) ((L i).comp (g t)) t) :
    HasFDerivAt f (g a) a := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hclose : ∀ᶠ t in 𝓝 a, ‖g t-g a‖ < ε :=
    by simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hg) ε hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) hclose)
  filter_upwards [Metric.ball_mem_nhds a hδ] with t ht
  apply hnorm _ _ (mul_nonneg hε.le (norm_nonneg _))
  intro i
  let v : Z → G := fun s => L i (f s) - L i (g a (s-a))
  have hv s (hs : s ∈ ball a δ) :
      HasFDerivAt v ((L i).comp (g s-g a)) s := by
    have hlin : HasFDerivAt (fun s : Z => L i (g a (s-a))) ((L i).comp (g a)) s :=
      ((L i).hasFDerivAt.comp s ((g a).hasFDerivAt.comp s ((hasFDerivAt_id s).sub_const a)))
    simpa only [v,ContinuousLinearMap.comp_sub] using! (hd s (hball hs).1 i).sub hlin
  have hb s (hs : s ∈ ball a δ) : ‖(L i).comp (g s-g a)‖ ≤ ε :=
    ((L i).opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _)).trans
      (by simpa using (hball hs).2.le))
  have h := (convex_ball a δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun s hs => (hv s hs).hasFDerivWithinAt) hb (mem_ball_self hδ) ht
  have heq : L i (f t-f a-g a (t-a)) = v t-v a := by
    simp only [v,map_sub,sub_self,sub_zero]
    abel
  rw [heq]
  exact h

end OAI.Analysis.PDE.Schauder
