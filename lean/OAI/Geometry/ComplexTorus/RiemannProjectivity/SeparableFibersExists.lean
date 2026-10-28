import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers

/-! # Separable Fibers Exists -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparableFibersExists.Constructions.SeparableFibers

noncomputable section

/-! # RiemannProjectivity: generic monic equations with one root per fiber point -/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem exists_generic_equation {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {z₀ : ℂ}
    (hlocal : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z₀))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (k : ℕ) (V : Set (Fin n → ℂ))
        (Q : (Fin n → ℂ) → ℂ[X]) (c : (Fin n → ℂ) → ℂ),
      0 < R ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ c V ∧
      V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) {y | y ∈ V ∧ c y ≠ 0}) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Monic ∧ (Q y).natDegree = k ∧ (Q y).Separable ∧
        (∀ z, (Q y).eval z = 0 → z ∈ ball z₀ R) ∧
        ∀ z ∈ closedBall z₀ R, (y, z) ∈ S ↔ (Q y).eval z = 0 := by
  obtain ⟨R, d, m, U, P, hR, hU, hxU, hcoeff, hdegree, hP, heq⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers.Constructions.Preparation.polynomial_equations_of_finite_fiber hlocal hfinite
  obtain ⟨k, Q, c, W, hW, hxW, hWU, hc, hcn, hQcoeff, hQ⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies.Constructions.GenericPolynomial.exists_monic_separable_common_root_family P hU hxU d hcoeff hdegree
      (fun y hy => ⟨0, (hP y hy).1.ne_zero⟩)
  obtain ⟨V, hV, hxV, hVW, hdense⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hW hxW hc hcn
  refine ⟨R, k, V, Q, c, hR, hV, hxV, hc.mono hVW, hdense,
    fun j => (hQcoeff j).mono (fun y hy => ⟨hVW hy.1, hy.2⟩), ?_⟩
  intro y hy hcy
  obtain ⟨hm, hd, hs, hroots⟩ := hQ y (hVW hy) hcy
  refine ⟨hm, hd, hs, ?_, ?_⟩
  · intro z hz
    exact (hP y (hWU (hVW hy))).2.2 z (((hroots z).mpr hz) 0)
  · intro z hz
    exact (heq y (hWU (hVW hy)) z hz).trans (hroots z)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparableFibersExists.Constructions.SeparableFibers
