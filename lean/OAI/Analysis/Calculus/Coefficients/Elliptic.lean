import OAI.Analysis.Calculus.Coefficients.Composition
import OAI.Analysis.PDE.Dirichlet.LatticeHolder

open Set Filter Metric Module InnerProductSpace
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem elliptic_lower_bound_of_norm_sub_le
    (A B : H →L[ℝ] H) {lam ε : ℝ}
    (hA : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A v)) (hAB : ‖A-B‖ ≤ ε) (v : H) :
    (lam-ε)*‖v‖^2 ≤ inner ℝ v (B v) := by
  have hi : inner ℝ v (A v)-inner ℝ v (B v) ≤ ε*‖v‖^2 := by
    calc
      inner ℝ v (A v)-inner ℝ v (B v) = inner ℝ v ((A-B) v) := by
        simp only [sub_apply,inner_sub_right]
      _ ≤ |inner ℝ v ((A-B) v)| := le_abs_self _
      _ ≤ ‖v‖*‖(A-B) v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖*(‖A-B‖*‖v‖) := mul_le_mul_of_nonneg_left ((A-B).le_opNorm v) (norm_nonneg _)
      _ ≤ ‖v‖*(ε*‖v‖) := by gcongr
      _ = ε*‖v‖^2 := by ring
  nlinarith [hA v]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- Uniform convergence on compact sets retains coercivity on one fixed
open neighborhood of a compact set, for a common tail of the sequence. -/
theorem compact_elliptic_neighborhood
    (A : E → H →L[ℝ] H) (hA : Continuous A)
    (a : ℕ → E → H →L[ℝ] H) {K : Set E} (_ : IsCompact K)
    (hc : TendstoUniformlyOn a A atTop (cthickening 1 K))
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ K, ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A x v)) :
    ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ cthickening 1 K ∧
      ∃ N : ℕ, ∀ j, N ≤ j → ∀ x ∈ O, ∀ v,
        (lam/2)*‖v‖^2 ≤ inner ℝ v (a j x v) := by
  let O : Set E := ⋃ x : K, ball (x : E) 1 ∩ A ⁻¹' ball (A x) (lam/4)
  have ho : IsOpen O := isOpen_iUnion (fun x ↦ isOpen_ball.inter (hA.isOpen_preimage _ isOpen_ball))
  have hKO : K ⊆ O := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,⟨by simp,by simpa using (by linarith : (0 : ℝ) < lam/4)⟩⟩
  have hOT : O ⊆ cthickening 1 K := by
    intro x hx
    obtain ⟨y,hy,_⟩ := mem_iUnion.mp hx
    exact ((closedBall_subset_cthickening_singleton _ _).trans
      (cthickening_subset_of_subset 1 (singleton_subset_iff.mpr y.property))) (ball_subset_closedBall hy)
  have hc' := Metric.tendstoUniformlyOn_iff.mp hc (lam/4) (by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hc'
  refine ⟨O,ho,hKO,hOT,N,?_⟩
  intro j hj x hx v
  obtain ⟨y,hy,hyA⟩ := mem_iUnion.mp hx
  have hxy : ‖A y-a j x‖ ≤ lam/2 := by
    have h₁ : ‖A y-A x‖ < lam/4 := by
      simpa only [mem_preimage,mem_ball,dist_eq_norm,norm_sub_rev] using hyA
    have h₂ : ‖A x-a j x‖ < lam/4 := by
      simpa only [dist_eq_norm] using hN j hj x (hOT hx)
    exact (norm_sub_le_norm_sub_add_norm_sub (A y) (A x) (a j x)).trans (by linarith)
  have h := elliptic_lower_bound_of_norm_sub_le (A y) (a j x) (hell y y.property) hxy v
  convert h using 1 ; ring

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
open OAI.Analysis.PDE.Dirichlet

omit [ProperSpace E] in
/-- Saturation of the same coercive neighborhood by the given lattice.
No compactness of the full periodic domain is asserted. -/
theorem periodic_elliptic_neighborhood
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (A : E → H →L[ℝ] H) (hA : Continuous A)
    (a : ℕ → E → H →L[ℝ] H) (hap : ∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (a j))
    {K D : Set E} (hK : IsCompact K)
    (hrep : ∀ x ∈ D, OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x ∈ K)
    (hc : TendstoUniformlyOn a A atTop (cthickening 1 K))
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ K, ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A x v)) :
    ∃ O : Set E, IsOpen O ∧ D ⊆ O ∧
      ∃ N : ℕ, ∀ j, N ≤ j → ∀ x ∈ O, ∀ v,
        (lam/2)*‖v‖^2 ≤ inner ℝ v (a j x v) := by
  obtain ⟨W,hW,hKW,_,N,hN⟩ := compact_elliptic_neighborhood A hA a hK hc hlam hell
  let O : Set E := ⋃ l : Submodule.span ℤ (range b), (fun x ↦ e.symm ((l : P),0)+x) ⁻¹' W
  have ho : IsOpen O := isOpen_iUnion (fun l ↦ hW.preimage (continuous_const.add continuous_id))
  refine ⟨O,ho,?_,N,?_⟩
  · intro x hx
    let l : Submodule.span ℤ (range b) := -ZSpan.floor b (e x).1
    apply mem_iUnion.mpr
    refine ⟨l,?_⟩
    change e.symm ((l : P),0)+x ∈ W
    have heq : e.symm ((l : P),0)+x = OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x := by
      rw [← OAI.Analysis.PDE.Dirichlet.lattice_translate_eq]
      simp only [l,OAI.Analysis.PDE.Dirichlet.latticeRepresentative,ZSpan.fract_apply,Submodule.coe_neg,sub_eq_add_neg]
    rw [heq]
    exact hKW (hrep x hx)
  · intro j hj x hx v
    obtain ⟨l,hl⟩ := mem_iUnion.mp hx
    have h := hN j hj (e.symm ((l : P),0)+x) hl v
    have hp := hap j x l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at hp
    rwa [hp] at h

end OAI.Analysis.Calculus.Coefficients
