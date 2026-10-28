import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateLifting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedReduction

/-! # Divided Coordinate Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift

noncomputable section

/-!
# IntegralComparison: étale charts lift uniquely into the native free divided-power algebra
-/

universe u

variable (R σ C T : Type u) [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R T] (I : Ideal T)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra T (σ →₀ T)

local instance scalarAlgebra : Algebra R G := inferInstance

local instance scalarTower : IsScalarTower R T G := inferInstance

def reduction : G →ₐ[R] T ⧸ I where
  toRingHom := Free.DividedReduction.reduction T σ I
  commutes' r := Free.DividedReduction.reduction_coefficient T σ I (algebraMap R T r)

def coordinates (l : C →ₐ[R] T) (i : σ) : G :=
  algebraMap T G (l (algebraMap P C (MvPolynomial.X i))) + AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i

omit [IsScalarTower R (MvPolynomial σ R) C] in
theorem coordinates_reduction (l : C →ₐ[R] T) (i : σ) :
    reduction R σ T I (coordinates R σ C T l i) =
      Ideal.Quotient.mk I (l (algebraMap P C (MvPolynomial.X i))) := by
  change Free.DividedReduction.reduction T σ I
    (algebraMap T G (l (algebraMap P C (MvPolynomial.X i))) + AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) = _
  rw [map_add, Free.DividedReduction.reduction_coefficient,
    Free.DividedReduction.reduction_generator T σ I 1 (by decide), add_zero]

theorem existsUnique_lift [Algebra.Etale (MvPolynomial σ R) C]
    (p : ℕ) [Fact p.Prime] (δ : DividedPowers I) (hp : IsNilpotent (p : T)) (l : C →ₐ[R] T) :
    ∃! f : C →ₐ[R] G, (reduction R σ T I).comp f = (Ideal.Quotient.mkₐ R I).comp l ∧
      ∀ i, f (algebraMap P C (MvPolynomial.X i)) = coordinates R σ C T l i :=
  CoordinateLifting.existsUnique_lift R σ C G (T ⧸ I) (reduction R σ T I)
    (Free.DividedReduction.reduction_surjective T σ I)
    (fun x hx => Free.DividedReduction.kernel_nil T σ I p δ hp x hx)
    ((Ideal.Quotient.mkₐ R I).comp l) (coordinates R σ C T l) (coordinates_reduction R σ C T I l)

variable [Algebra.Etale (MvPolynomial σ R) C]
  (p : ℕ) [Fact p.Prime] (δ : DividedPowers I) (hp : IsNilpotent (p : T)) (l : C →ₐ[R] T)

def lift : C →ₐ[R] G := (existsUnique_lift R σ C T I p δ hp l).choose

theorem lift_reduction : (reduction R σ T I).comp (lift R σ C T I p δ hp l) = (Ideal.Quotient.mkₐ R I).comp l :=
  (existsUnique_lift R σ C T I p δ hp l).choose_spec.1.1

theorem lift_coordinate (i : σ) :
    lift R σ C T I p δ hp l (algebraMap P C (MvPolynomial.X i)) = coordinates R σ C T l i :=
  (existsUnique_lift R σ C T I p δ hp l).choose_spec.1.2 i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift
