import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots

/-! # Generic Fibers -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericFibers.Constructions.Preparation

noncomputable section

/-!
# A monic equation for generic finite analytic fibers

The prepared polynomial equations yield one monic equation on a dense open
part of a neighborhood. Its roots lie in the preparation disk and describe
exactly the original analytic set there.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem generic_monic_equation_of_finite_fiber {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {z₀ : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z₀))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (k : ℕ) (V : Set (Fin n → ℂ))
        (Q : (Fin n → ℂ) → ℂ[X]) (c : (Fin n → ℂ) → ℂ),
      0 < R ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ c V ∧
      V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
      IsOpen {y | y ∈ V ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) {y | y ∈ V ∧ c y ≠ 0}) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Monic ∧ (Q y).natDegree = k ∧ (Q y).Separable ∧
        (∀ z, (Q y).eval z = 0 → z ∈ ball z₀ R) ∧
        (∀ j, ‖(Q y).coeff j‖ ≤ (k.choose j : ℝ) * (max 1 (‖z₀‖ + R)) ^ k) ∧
        {z : ℂ | z ∈ closedBall z₀ R ∧ (y, z) ∈ S}.ncard = k ∧
        ∀ z ∈ closedBall z₀ R, (y, z) ∈ S ↔ (Q y).eval z = 0 := by
  obtain ⟨R, d, m, U, P, hR, hU, hxU, hcoeff, hdegree, hP, heq⟩ :=
    PolynomialFibers.Constructions.Preparation.polynomial_equations_of_finite_fiber hlocal hfinite
  obtain ⟨k, Q, c, W, hW, hxW, hWU, hc, hcn, hQcoeff, hQ⟩ :=
    SquarefreeFamilies.Constructions.GenericPolynomial.exists_monic_separable_common_root_family P hU hxU d hcoeff hdegree
      (fun y hy => ⟨0, (hP y hy).1.ne_zero⟩)
  obtain ⟨V, hV, hxV, hVW, hdense⟩ :=
    GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hW hxW hc hcn
  have hcV := hc.mono hVW
  have hopen : IsOpen {y | y ∈ V ∧ c y ≠ 0} := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    filter_upwards [hV.mem_nhds hy.1,
      (hcV.differentiableAt (hV.mem_nhds hy.1)).continuousAt.eventually_ne hy.2] with z hz hzc
    exact ⟨hz, hzc⟩
  refine ⟨R, k, V, Q, c, hR, hV, hxV, hcV, hdense, hopen,
    fun j => (hQcoeff j).mono (fun y hy => ⟨hVW hy.1, hy.2⟩), ?_⟩
  intro y hy hcy
  obtain ⟨hmonic, hdeg, hsep, hroots⟩ := hQ y (hVW hy) hcy
  have hrootBall (z : ℂ) (hz : (Q y).eval z = 0) : z ∈ ball z₀ R := by
    exact (hP y (hWU (hVW hy))).2.2 z (((hroots z).mpr hz) 0)
  have hzero (z : ℂ) (hz : z ∈ closedBall z₀ R) : (y, z) ∈ S ↔ (Q y).eval z = 0 := by
    exact (heq y (hWU (hVW hy)) z hz).trans (hroots z)
  refine ⟨hmonic, hdeg, hsep, hrootBall, ?_, ?_, hzero⟩
  · intro j
    rw [← hdeg]
    apply MonicRoots.Constructions.RootPolynomials.norm_coeff_le_of_roots_bounded hmonic
    intro z hz
    have hdist := mem_ball_iff_norm.mp (hrootBall z hz)
    have hnorm := norm_le_norm_sub_add z z₀
    linarith
  · have hset : {z : ℂ | z ∈ closedBall z₀ R ∧ (y, z) ∈ S} =
        {z : ℂ | (Q y).eval z = 0} := by
      ext z
      constructor
      · intro hz
        exact (hzero z hz.1).mp hz.2
      · intro hz
        have hzb := ball_subset_closedBall (hrootBall z hz)
        exact ⟨hzb, (hzero z hzb).mpr hz⟩
    rw [hset, MonicRoots.Constructions.RootPolynomials.ncard_zero_set hmonic.ne_zero hsep, hdeg]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericFibers.Constructions.Preparation
