import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift

/-! # Divided Coordinate Retraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateRetraction

noncomputable section

/-!
# IntegralComparison: the étale divided-coordinate lift retracts to the original chart map
-/

universe u

variable (R σ C T : Type u) [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R T] (I : Ideal T)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra T (σ →₀ T)

attribute [local instance] DividedCoordinateLift.scalarAlgebra DividedCoordinateLift.scalarTower

def augmentation : G →ₐ[R] T := (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation T σ).restrictScalars R

omit [IsScalarTower R (MvPolynomial σ R) C] in
theorem augmentation_coordinates (l : C →ₐ[R] T) (i : σ) :
    augmentation R σ T (DividedCoordinateLift.coordinates R σ C T l i) =
      l (algebraMap P C (MvPolynomial.X i)) := by
  change AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation T σ
    (algebraMap T G (l (algebraMap P C (MvPolynomial.X i))) + AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ 1 i) = _
  rw [map_add, AlgHom.commutes, Algebra.algebraMap_self_apply, AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation_generator,
    DividedPowers.dpow_eval_zero _ (by decide : (1 : ℕ) ≠ 0), add_zero]

theorem augmentation_lift [Algebra.Etale (MvPolynomial σ R) C]
    (p : ℕ) [Fact p.Prime] (δ : DividedPowers I) (hp : IsNilpotent (p : T))
    (l : C →ₐ[R] T) (f : C →ₐ[R] G)
    (hf : (DividedCoordinateLift.reduction R σ T I).comp f = (Ideal.Quotient.mkₐ R I).comp l)
    (hx : ∀ i, f (algebraMap P C (MvPolynomial.X i)) = DividedCoordinateLift.coordinates R σ C T l i) :
    (augmentation R σ T).comp f = l := by
  apply CoordinateLifting.lift_unique R σ C T (T ⧸ I) (Ideal.Quotient.mkₐ R I)
    (fun x h => DividedPower.Nilpotence.nilpotent_of_mem δ p (Fact.out : p.Prime).pos hp
      (Ideal.Quotient.eq_zero_iff_mem.mp h)) ((augmentation R σ T).comp f) l
  · exact AlgHom.ext (fun c => AlgHom.congr_fun hf c)
  · intro i
    change augmentation R σ T (f (algebraMap P C (MvPolynomial.X i))) = _
    rw [hx]
    exact augmentation_coordinates R σ C T l i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateRetraction
