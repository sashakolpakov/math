import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt

/-! # Polynomial Fibers -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers.Constructions.Preparation

noncomputable section

/-!
# Polynomial equations for finite analytic fibers

Prepare one defining equation and replace every remaining equation by its
contour remainder. The resulting polynomials have holomorphic coefficients,
a common degree bound, and exactly the original common zero set locally.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

theorem polynomial_equations_of_finite_fiber {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {c : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, c))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (d m : ℕ) (U : Set (Fin n → ℂ))
        (Q : Fin (m + 1) → (Fin n → ℂ) → Polynomial ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧
      (∀ i k, DifferentiableOn ℂ (fun y => (Q i y).coeff k) U) ∧
      (∀ i y, y ∈ U → (Q i y).natDegree ≤ d) ∧
      (∀ y ∈ U, (Q 0 y).Monic ∧ (Q 0 y).natDegree = d ∧
        ∀ z, (Q 0 y).eval z = 0 → z ∈ ball c R) ∧
      ∀ y ∈ U, ∀ z ∈ closedBall c R, (y, z) ∈ S ↔ ∀ i, (Q i y).eval z = 0 := by
  obtain ⟨R, d, m, U, W, P, f, hR, hU, hx, hW, hUW, hcoeff, hP, hf, heq⟩ :=
    LocalPreparation.Constructions.Preparation.polynomial_constraint_of_finite_fiber hlocal hfinite
  let Q : Fin (m + 1) → (Fin n → ℂ) → Polynomial ℂ :=
    Fin.cons P (fun i y => ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial d (P y) (fun z => f i (y, z)) c R)
  have hboundary (y : Fin n → ℂ) (hy : y ∈ U) :
      ∀ z ∈ sphere c R, (P y).eval z ≠ 0 := by
    intro z hz hzero
    exact (ne_of_lt (mem_ball.mp ((hP y hy).2.2 z hzero))) (mem_sphere.mp hz)
  have hr (i : Fin m) (y : Fin n → ℂ) (hy : y ∈ U) (z : ℂ)
      (hz : (P y).eval z = 0) : (Q i.succ y).eval z = f i (y, z) := by
    have hanalytic := RootFamiliesAt.Constructions.RootFamilies.analyticOnNhd_slice hW (hf i) y
      (fun w hw => hUW ⟨hy, hw⟩)
    exact ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial_eval_at_root (P y) (hP y hy).2.1 hR
      hanalytic.differentiableOn (hboundary y hy) ((hP y hy).2.2 z hz) hz
  refine ⟨R, d, m, U, Q, hR, hU, hx, ?_, ?_, hP, ?_⟩
  · intro i
    refine Fin.cases hcoeff (fun j k => ?_) i
    exact ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_remainderPolynomial_coeff hW (hf j) hU hcoeff
      (fun y hy => (hP y hy).2.1.le) hR.le
      (fun p hp => hUW ⟨hp.1, sphere_subset_closedBall hp.2⟩) hboundary k
  · intro i
    refine Fin.cases (fun y hy => (hP y hy).2.1.le) (fun j y _ => ?_) i
    exact ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial_natDegree_le d (P y) (fun z => f j (y, z)) c R
  · intro y hy z hz
    rw [heq y hy z hz]
    constructor
    · rintro ⟨hpz, hfz⟩ i
      refine Fin.cases hpz (fun j => ?_) i
      rw [hr j y hy z hpz]
      exact hfz j
    · intro h
      have hpz : (P y).eval z = 0 := h 0
      refine ⟨hpz, fun j => ?_⟩
      rw [← hr j y hy z hpz]
      exact h j.succ

/-- The projection of the local analytic set is the common-root locus of
a concrete finite family of polynomials with holomorphic coefficients. -/
theorem local_projection_as_common_roots {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {c : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, c))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (d m : ℕ) (U : Set (Fin n → ℂ))
        (Q : Fin (m + 1) → (Fin n → ℂ) → Polynomial ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧
      (∀ i k, DifferentiableOn ℂ (fun y => (Q i y).coeff k) U) ∧
      (∀ i y, y ∈ U → (Q i y).natDegree ≤ d) ∧
      (∀ y ∈ U, (Q 0 y).Monic ∧ (Q 0 y).natDegree = d) ∧
      ∀ y ∈ U, (∃ z ∈ closedBall c R, (y, z) ∈ S) ↔ ∃ z, ∀ i, (Q i y).eval z = 0 := by
  obtain ⟨R, d, m, U, Q, hR, hU, hx, hcoeff, hdeg, hQ, heq⟩ :=
    polynomial_equations_of_finite_fiber hlocal hfinite
  refine ⟨R, d, m, U, Q, hR, hU, hx, hcoeff, hdeg,
    fun y hy => ⟨(hQ y hy).1, (hQ y hy).2.1⟩, ?_⟩
  intro y hy
  constructor
  · rintro ⟨z, hz, hzs⟩
    exact ⟨z, (heq y hy z hz).mp hzs⟩
  · rintro ⟨z, hz⟩
    have hzb := ball_subset_closedBall ((hQ y hy).2.2 z (hz 0))
    exact ⟨z, hzb, (heq y hy z hzb).mpr hz⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers.Constructions.Preparation
