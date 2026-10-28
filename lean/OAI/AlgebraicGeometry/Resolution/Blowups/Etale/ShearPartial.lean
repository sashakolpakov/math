import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Shear

/-! # Shear Partial -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearPartial.Construction

noncomputable section

/-! The canonical coordinate partial after a shear is the sum of two original partials. -/

variable {σ k R S : Type*} [Field k] [CommRing R] [CommRing S]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k R] [Algebra k S]
  [IsScalarTower k (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) S]
  [DecidableEq σ]

/-- The sum of the two original coordinate partials differentiates the fixed
coordinate to one and every sheared complement to zero. -/
theorem etale_shear_sum_partial_coordinates (i j : σ) (hij : i ≠ j) (a : σ) :
    (DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i + DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j)
      (if a = j then
        algebraMap (MvPolynomial σ k) R (MvPolynomial.X j) -
          algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
        else algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) =
      if i = a then 1 else 0 := by
  by_cases haj : a = j
  · subst a
    simp [TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, hij, Ne.symm hij]
  · rw [ite_eq_right haj, Derivation.add_apply, TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X,
      TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right (Ne.symm haj), add_zero]

/-- On a copy with the sheared coordinate presentation, the canonical partial
in the fixed direction is the transported sum of the two original partials. -/
theorem etale_shear_partial_formula (e : R ≃ₐ[k] S) (i j : σ) (hij : i ≠ j)
    (hcoords : ∀ a : σ, algebraMap (MvPolynomial σ k) S (MvPolynomial.X a) =
      e (if a = j then algebraMap (MvPolynomial σ k) R (MvPolynomial.X j) -
        algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
        else algebraMap (MvPolynomial σ k) R (MvPolynomial.X a))) (x : R) :
    DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := S) i (e x) =
      e (DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i x +
        DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j x) := by
  let D := DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i + DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j
  have he : Relative.DifferentialEquiv.Construction.transportRelativeDerivation e D = DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := S) i := by
    apply ModuleDerivations.Construction.etale_relative_derivation_ext (σ := σ)
    intro a
    rw [hcoords a, Relative.DifferentialEquiv.Construction.transportRelativeDerivation_map]
    change e (D _) = _
    rw [etale_shear_sum_partial_coordinates i j hij a]
    rw [← hcoords a, TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X]
    split_ifs <;> simp
  rw [← he, Relative.DifferentialEquiv.Construction.transportRelativeDerivation_map]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearPartial.Construction
