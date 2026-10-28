import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing
import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC

/-! # Cone Chart By -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction

noncomputable section

/-! # RiemannProjectivity: restricting the cone algebra to a normalized projective chart -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {ι : Type*}

def chart (S : Set (ι → ℂ)) (i : ι) : Set ({j : ι // j ≠ i} → ℂ) :=
  {x | AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x ∈ S}

def variableClass (S : Set (ι → ℂ)) (i : ι) : AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

abbrev patchRing (S : Set (ι → ℂ)) (i : ι) := Localization.Away (variableClass S i)

def polynomialMap (i : ι) : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial {j : ι // j ≠ i} ℂ :=
  { AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i with commutes' c := AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_C i c }

def restriction (S : Set (ι → ℂ)) (i : ι) : AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S →ₐ[ℂ] AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (chart S i) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp (polynomialMap i)) (by
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    intro x hx
    change MvPolynomial.eval x (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p) = 0
    rw [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize]
    exact hp (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x) hx)

theorem restriction_variable_self (S : Set (ι → ℂ)) (i : ι) :
    restriction S i (variableClass S i) = 1 := by
  change Ideal.Quotient.mk _ (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X i)) = 1
  rw [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self, map_one]

theorem restriction_variable (S : Set (ι → ℂ)) (i j : ι) (hj : j ≠ i) :
    restriction S i (variableClass S j) = Ideal.Quotient.mk _ (MvPolynomial.X ⟨j, hj⟩) := by
  change Ideal.Quotient.mk _ (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X j)) = _
  rw [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne i j hj]

def localizedRestriction (S : Set (ι → ℂ)) (i : ι) : patchRing S i →ₐ[ℂ] AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (chart S i) :=
  IsLocalization.Away.liftAlgHom (f := restriction S i) (variableClass S i)
    (by rw [restriction_variable_self]; exact isUnit_one)

theorem localizedRestriction_algebraMap (S : Set (ι → ℂ)) (i : ι) (a : AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) :
    localizedRestriction S i (algebraMap (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (patchRing S i) a) = restriction S i a := by
  simp only [localizedRestriction, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

theorem chart_determined_by_polynomials (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (i : ι) (x : {j : ι // j ≠ i} → ℂ)
    (hx : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ (chart S i), MvPolynomial.eval x p = 0) :
    x ∈ chart S i := by
  apply hS
  intro p hp
  have hde : AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p ∈ MvPolynomial.vanishingIdeal ℂ (chart S i) := by
    intro y hy
    change MvPolynomial.eval y (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p) = 0
    rw [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize]
    exact hp (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i y) hy
  have h := hx (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p) hde
  rwa [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize] at h

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction
