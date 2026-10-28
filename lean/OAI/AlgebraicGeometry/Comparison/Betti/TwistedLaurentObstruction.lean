import OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentSplitting
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ProjectionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RemainderMultiples

/-! # Twisted Laurent Obstruction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentObstruction.Dolbeault

noncomputable section

/-! The actual finite Laurent obstruction vanishes precisely on sums
of the two holomorphic chart sections for a negative twist. -/

open _root_.Complex Set _root_.Metric _root_.Polynomial

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RemainderMultiples.Weierstrass OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

omit [FiniteDimensional ℂ P] in
theorem entireFamily_slice_holomorphic {G : P × ℂ → ℂ} {S : Set P}
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) {p : P} (hp : p ∈ S) :
    Differentiable ℂ (fun z => G (p, z)) := by
  rw [← differentiableOn_univ]
  exact hG.comp ((differentiable_const p).prodMk differentiable_id).differentiableOn
    (fun _ hz => ⟨hp, hz⟩)

omit [FiniteDimensional ℂ P] in
theorem negativeTwistLaurentRemainder_vanishes_of_decomposition
    {G a b : P × ℂ → ℂ} {S : Set P}
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    (ha : DifferentiableOn ℂ a (S ×ˢ univ)) (hb : DifferentiableOn ℂ b (S ×ˢ univ))
    {m : ℕ} (hm : 0 < m)
    (h : ∀ p ∈ S, ∀ z ≠ 0, G (p, z) = a (p, z) + (z ^ m)⁻¹ * b (p, z⁻¹))
    {p : P} (hp : p ∈ S) : TwistedLaurentSplitting.Dolbeault.negativeTwistLaurentRemainder G m p = 0 := by
  have hb' := entireFamily_slice_holomorphic hb hp
  have hmul : Differentiable ℂ (fun u => u ^ m * b (p, u)) := (differentiable_id.pow m).fun_mul hb'
  have hn := (Laurent.ProjectionNaturality.Dolbeault.laurentProjection_eq_of_decomposition (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic hG hp)
    (entireFamily_slice_holomorphic ha hp) hmul
    (by rw [zero_pow (Nat.ne_of_gt hm), zero_mul]) (fun z hz => by
      simpa only [inv_pow] using h p hp z hz)).2
  change ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial m ((X : Polynomial ℂ) ^ m)
    (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun z => G (p, z))) 0 1 = 0
  rw [hn]
  have hP (z : ℂ) (hz : z ∈ sphere 0 1) : ((X : Polynomial ℂ) ^ m).eval z ≠ 0 := by
    simp only [eval_pow, eval_X]
    apply pow_ne_zero
    have hnorm : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    exact norm_pos_iff.mp (hnorm.symm ▸ (by norm_num : 0 < (1 : ℝ)))
  simpa only [eval_pow, eval_X] using
    Holomorphic.RemainderMultiples.Weierstrass.remainderPolynomial_multiple_zero m ((X : Polynomial ℂ) ^ m) (fun u => b (p, u))
      hb'.differentiableOn hP

theorem negativeTwistLaurent_obstruction_iff {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) {m : ℕ} (hm : 0 < m) :
    (∀ p ∈ S, TwistedLaurentSplitting.Dolbeault.negativeTwistLaurentRemainder G m p = 0) ↔
      ∃ a b : P × ℂ → ℂ, DifferentiableOn ℂ a (S ×ˢ univ) ∧
        DifferentiableOn ℂ b (S ×ˢ univ) ∧
        ∀ p ∈ S, ∀ z ≠ 0, G (p, z) = a (p, z) + (z ^ m)⁻¹ * b (p, z⁻¹) := by
  constructor
  · intro hzero
    refine ⟨ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G, TwistedLaurentSplitting.Dolbeault.negativeTwistLaurentQuotient G m,
      ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily_holomorphic hS hG, TwistedLaurentSplitting.Dolbeault.negativeTwistLaurentQuotient_holomorphic hS hG m, ?_⟩
    intro p hp z hz
    simpa only [hzero p hp, eval_zero, add_zero] using TwistedLaurentSplitting.Dolbeault.negativeTwistLaurentSplitting_identity hS hG m hp hz
  · rintro ⟨a, b, ha, hb, h⟩ p hp
    exact negativeTwistLaurentRemainder_vanishes_of_decomposition hG ha hb hm h hp

end

end OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentObstruction.Dolbeault
