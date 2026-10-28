import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Schauder

/-- A pointwise derivative is a norm derivative when the candidate derivative
is norm-continuous and the evaluation family norms the ambient space. -/
theorem hasDerivAt_of_norming_family
    {F G I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : I → F →L[ℝ] G) (hL : ∀ i, ‖L i‖ ≤ 1)
    (hnorm : ∀ (v : F) (C : ℝ), 0 ≤ C → (∀ i, ‖L i v‖ ≤ C) → ‖v‖ ≤ C)
    {f g : ℝ → F} {U : Set ℝ} (hU : IsOpen U) {a : ℝ} (ha : a ∈ U)
    (hg : ContinuousAt g a)
    (hd : ∀ t ∈ U, ∀ i, HasDerivAt (fun s => L i (f s)) (L i (g t)) t) :
    HasDerivAt f (g a) a := by
  rw [hasDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hclose : ∀ᶠ t in 𝓝 a, ‖g t-g a‖ < ε :=
    by simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hg) ε hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) hclose)
  filter_upwards [Metric.ball_mem_nhds a hδ] with t ht
  apply hnorm _ _ (mul_nonneg hε.le (norm_nonneg _))
  intro i
  let v : ℝ → G := fun s => L i (f s) - (s-a) • L i (g a)
  have hv s (hs : s ∈ ball a δ) : HasDerivAt v (L i (g s-g a)) s := by
    have hlin : HasDerivAt (fun s : ℝ => (s-a) • L i (g a)) (L i (g a)) s := by
      simpa using ((hasDerivAt_id s).sub_const a).smul_const (L i (g a))
    simpa only [v,map_sub,Pi.sub_apply] using! (hd s (hball hs).1 i).sub hlin
  have hb s (hs : s ∈ ball a δ) : ‖L i (g s-g a)‖ ≤ ε :=
    ((L i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _)).trans
      (by simpa using (hball hs).2.le))
  have h := (convex_ball a δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hv s hs).hasDerivWithinAt) hb (mem_ball_self hδ) ht
  have heq : L i (f t-f a-(t-a) • g a) = v t-v a := by
    simp only [v,map_sub,map_smul,sub_self,zero_smul,sub_zero]
    abel
  rw [heq]
  exact h

end OAI.Analysis.PDE.Schauder
