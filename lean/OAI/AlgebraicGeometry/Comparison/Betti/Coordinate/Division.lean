import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters

/-! # Division -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.Division.Weierstrass

noncomputable section

/-! A holomorphic family differs from its central slice by its centered
coordinate times a jointly holomorphic function. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem exists_product_closedDisk {W : Set (E × ℂ)} (hW : IsOpen W)
    {x : E} {c : ℂ} (hxc : (x, c) ∈ W) :
    ∃ (R : ℝ) (U : Set E), 0 < R ∧ IsOpen U ∧ x ∈ U ∧ U ×ˢ closedBall c R ⊆ W := by
  have hn := (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hxc
  obtain ⟨R, hR, hball⟩ := nhds_basis_closedBall.mem_iff.mp hn
  have hb : ({x} : Set E) ×ˢ closedBall c R ⊆ W := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    rcases mem_singleton_iff.mp hy with rfl
    exact hball hz
  obtain ⟨U, V, hU, _, hx, hV, hUV⟩ := generalized_tube_lemma
    isCompact_singleton (isCompact_closedBall c R) hW hb
  exact ⟨R, U, hR, hU, hx (mem_singleton x), fun p hp => hUV ⟨hp.1, hV hp.2⟩⟩

theorem coordinate_division
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {U : Set E} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hUW : U ×ˢ closedBall c R ⊆ W) :
    ∃ Q : E × ℂ → ℂ, DifferentiableOn ℂ Q (U ×ˢ ball c R) ∧
      ∀ y ∈ U, ∀ w ∈ ball c R, F (y, w) = F (y, c) + (w - c) * Q (y, w) := by
  let P : E → ℂ[X] := fun _ => X - C c
  have hc : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U :=
    fun k => differentiableOn_const _
  have hd : ∀ y ∈ U, (P y).natDegree = 1 := fun _ _ => natDegree_X_sub_C c
  have hn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0 := by
    intro y hy z hz
    have hzc : z ≠ c := ne_of_mem_sphere hz (ne_of_gt hR)
    simpa only [P, eval_sub, eval_X, eval_C, sub_ne_zero] using hzc
  obtain ⟨hQ, _, hcoeff, he⟩ := Holomorphic.DivisionParameters.Weierstrass.holomorphic_family_division hW hF hU hc hd hR hUW hn
  refine ⟨fun p => Holomorphic.DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2, hQ, ?_⟩
  intro y hy w hw
  let A := ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial 1 (P y) (fun z => F (y, z)) c R
  have hA : A = C (A.coeff 0) := by
    ext k
    by_cases hk : k = 0
    · subst k
      simp only [coeff_C_zero]
    · rw [coeff_C, ite_eq_right hk]
      exact hcoeff y hy k (by omega)
  have hcenter := he y hy c (mem_ball_self hR)
  have hw' := he y hy w hw
  change F (y, c) = A.eval c + _ at hcenter
  change F (y, w) = A.eval w + _ at hw'
  rw [hA] at hcenter hw'
  simp only [P, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero] at hcenter
  simpa only [P, eval_C, eval_sub, eval_X, ← hcenter] using hw'

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.Division.Weierstrass
