import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Component
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface

/-! # Component Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentComparison.Construction

noncomputable section

/-! Canonical coefficient component centers agree on actual boundary-preserving ambient neighborhoods. -/

universe u

variable {σ k R C : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

theorem coefficient_component_centers_locally_agree
    (J : Ideal R) (B : Finset σ) (i : σ) (hiB : i ∉ B) (z : R) (E : Derivation k R R)
    (hE : E z = 1) (n : ℕ) (r : R →ₐ[k] C)
    (htrans : ∃ j : σ, j ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j z) ≠ 0)
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = r z) :
    let x := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
    let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
    let I := ComponentNaturality.Construction.coefficientComponentCenter k x H (n + 1)
    let L := ComponentNaturality.Construction.coefficientComponentCenter k z H (n + 1)
    J ≤ I ^ (n + 1) ∧ J ≤ L ^ (n + 1) ∧ Algebra.Smooth k (R ⧸ I) ∧ Algebra.Smooth k (R ⧸ L) ∧
      ∃ s : R, r s ≠ 0 ∧ I.map (algebraMap R (Localization.Away s)) =
        L.map (algebraMap R (Localization.Away s)) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ k) R
  let : Algebra.Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k R := Algebra.Smooth.comp k (MvPolynomial σ k) R
  let x := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
  let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
  let F := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i
  have hF : F x = 1 := by
    change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i
      (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = 1
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_left rfl]
  let : Algebra.Smooth k (R ⧸ Ideal.span {x}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one F x hF
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E z hE
  have hHI := Component.Construction.coefficientComponentCenter_permissible k F x hF H (n + 1)
  have hHL := Component.Construction.coefficientComponentCenter_permissible k E z hE H (n + 1)
  have hsI := Component.Construction.coefficientComponentCenter_smooth k x H (n + 1)
  have hsL := Component.Construction.coefficientComponentCenter_smooth k z H (n + 1)
  have hJI := (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans hHI
  have hJL := (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans hHL
  refine ⟨hJI, hJL, hsI, hsL, ?_⟩
  obtain ⟨U, instU, instkU, f, g, v, heq, hf, hg, _, _, _, _, _, _, hcoeff, hdescent⟩ :=
    Boundary.CoefficientComparison.Construction.exists_boundary_coefficient_comparison J B i hiB z n r htrans hi hz hpoint
  let : CommRing U := instU
  let : Algebra k U := instkU
  exact hdescent _ _ hJI hJL (IsNoetherian.noetherian _) (IsNoetherian.noetherian _)
    (ComponentNaturality.Construction.coefficientComponentCenter_compared_quotients f g hf hg x z heq H H (n + 1) hcoeff)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentComparison.Construction
