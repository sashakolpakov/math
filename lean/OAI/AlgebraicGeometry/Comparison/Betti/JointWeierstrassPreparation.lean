import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters
import OAI.AlgebraicGeometry.Comparison.Betti.DivisionQuotientUnit
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation

/-! # Joint Weierstrass Preparation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.JointWeierstrassPreparation

noncomputable section

/-! Polynomial preparation with a jointly holomorphic nonvanishing factor.
The factor is the actual parameter-dependent contour quotient. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

theorem exists_joint_polynomial_preparation
    {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ} {W : Set ((Fin n → ℂ) × ℂ)}
    (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {x : Fin n → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W)
    (hn : ∀ z ∈ sphere c R, F (x, z) ≠ 0) :
    ∃ (d : ℕ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → Polynomial ℂ)
        (q : (Fin n → ℂ) × ℂ → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ×ˢ closedBall c R ⊆ W ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      (∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d ∧
        ∀ z, (P y).eval z = 0 → z ∈ ball c R) ∧
      DifferentiableOn ℂ q (U ×ˢ ball c R) ∧
      (∀ p ∈ U ×ˢ ball c R, q p ≠ 0) ∧
      ∀ p ∈ U ×ˢ ball c R, F p = (P p.1).eval p.2 * q p := by
  obtain ⟨d, U, P, hU, hx, hUW, hcoeff, hdata⟩ :=
    ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation.Constructions.Preparation.exists_polynomial_preparation hW hF hR hbase hn
  have hPn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0 := by
    intro y hy z hz he
    have hb := (hdata y hy).2.2.1 z he
    exact (ne_of_lt (mem_ball.mp hb)) (mem_sphere.mp hz)
  let q : (Fin n → ℂ) × ℂ → ℂ := fun p =>
    Holomorphic.DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2
  have hq : DifferentiableOn ℂ q (U ×ˢ ball c R) :=
    Holomorphic.DivisionParameters.Weierstrass.differentiableOn_divisionQuotient hW hF hU hcoeff
      (fun y hy => (hdata y hy).2.1.le) hR.le
      (fun p hp => hUW ⟨hp.1, sphere_subset_closedBall hp.2⟩) hPn
  have hunit : ∀ y ∈ U, ∀ w ∈ ball c R, q (y, w) ≠ 0 ∧ F (y, w) = (P y).eval w * q (y, w) := by
    intro y hy w hw
    obtain ⟨_, _, _, u, hu, hun, hfactor⟩ := hdata y hy
    have hboundary : ∀ z ∈ sphere c R, F (y, z) = (P y).eval z * u z :=
      fun z hz => (hfactor z (sphere_subset_closedBall hz)).eq_of_nhds
    have he : q (y, w) = u w := DivisionQuotientUnit.Weierstrass.divisionQuotient_eq_of_boundary (P y) (fun z => F (y, z)) u
      c R w hR.le hu.differentiableOn (hPn y hy) hboundary hw
    exact ⟨he ▸ hun w (ball_subset_closedBall hw),
      ((hfactor w (ball_subset_closedBall hw)).eq_of_nhds).trans (congrArg (fun t => (P y).eval w * t) he.symm)⟩
  exact ⟨d, U, P, q, hU, hx, hUW, hcoeff,
    fun y hy => ⟨(hdata y hy).1, (hdata y hy).2.1, (hdata y hy).2.2.1⟩,
    hq, fun p hp => (hunit p.1 hp.1 p.2 hp.2).1,
    fun p hp => (hunit p.1 hp.1 p.2 hp.2).2⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.JointWeierstrassPreparation
