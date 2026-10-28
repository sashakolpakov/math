import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoefficientExtension
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericFibers

/-! # Extended Fibers -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ExtendedFibers.Constructions.Preparation

noncomputable section

/-!
# Holomorphic polynomial extensions of generic analytic fibers

The reduced monic equation of a generic finite analytic fiber extends to
the whole base neighborhood. Equality with the original analytic set is
asserted on the dense open complement of the exceptional set.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem extended_monic_equation_of_finite_fiber {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {z₀ : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z₀))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (k : ℕ) (V : Set (Fin n → ℂ))
        (Q : (Fin n → ℂ) → ℂ[X]) (c : (Fin n → ℂ) → ℂ),
      0 < R ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ c V ∧
      V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) V) ∧
      (∀ y ∈ V, (Q y).Monic ∧ (Q y).natDegree = k) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Separable ∧
        (∀ z, (Q y).eval z = 0 → z ∈ ball z₀ R) ∧
        ∀ z ∈ closedBall z₀ R, (y, z) ∈ S ↔ (Q y).eval z = 0 := by
  obtain ⟨R, k, U, P, c, hR, hU, hxU, hc, hdense, _, hcoeff, hP⟩ :=
    GenericFibers.Constructions.Preparation.generic_monic_equation_of_finite_fiber hlocal hfinite
  have hcn : ¬∀ᶠ y in 𝓝 x, c y = 0 := by
    intro hz
    obtain ⟨y, hy, hzy⟩ := ((mem_closure_iff_frequently.mp (hdense hxU)).and_eventually hz).exists
    exact hy.2 hzy
  have hbound (j : ℕ) : ∃ M : ℝ, ∀ y ∈ U, c y ≠ 0 → ‖(P y).coeff j‖ ≤ M := by
    refine ⟨(k.choose j : ℝ) * (max 1 (‖z₀‖ + R)) ^ k, ?_⟩
    intro y hy hcy
    exact (hP y hy hcy).2.2.2.2.1 j
  obtain ⟨V, Q, hV, hxV, hVU, hdenseV, hQcoeff, hQmonic, hQeq⟩ :=
    CoefficientExtension.Constructions.GenericPolynomial.exists_extended_monic_family hU hc hcoeff
      (fun y hy hcy => ⟨(hP y hy hcy).1, (hP y hy hcy).2.1⟩) hbound hxU hcn
  refine ⟨R, k, V, Q, c, hR, hV, hxV, hc.mono hVU, hdenseV, hQcoeff, hQmonic, ?_⟩
  intro y hy hcy
  rw [hQeq y hy hcy]
  obtain ⟨_, _, hsep, hroots, _, _, heq⟩ := hP y (hVU hy) hcy
  exact ⟨hsep, hroots, heq⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ExtendedFibers.Constructions.Preparation
