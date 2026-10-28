import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateRetraction

/-! # Divided Lift Ideal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal

noncomputable section

/-!
# IntegralComparison: the chosen étale lift differs from the original chart map by the PD ideal
-/

universe u

variable (R σ C T : Type u) [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R T] [Algebra.Etale (MvPolynomial σ R) C]
  (I : Ideal T) (p : ℕ) [Fact p.Prime] (δ : DividedPowers I)
  (hp : IsNilpotent (p : T)) (l : C →ₐ[R] T)

local notation "G" => DividedPowerAlgebra T (σ →₀ T)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedCoordinateLift.lift R σ C T I p δ hp l

attribute [local instance] DividedCoordinateLift.scalarAlgebra DividedCoordinateLift.scalarTower

theorem augmentation_comp : (DividedCoordinateRetraction.augmentation R σ T).comp e = l :=
  DividedCoordinateRetraction.augmentation_lift R σ C T I p δ hp l e
    (DividedCoordinateLift.lift_reduction R σ C T I p δ hp l)
    (DividedCoordinateLift.lift_coordinate R σ C T I p δ hp l)

theorem difference_mem (c : C) :
    e c - algebraMap T G (l c) ∈ AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal T σ I := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.ideal_eq_comap]
  change AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation T σ (e c - algebraMap T G (l c)) ∈ I
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hc : AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation T σ (e c) = l c :=
    AlgHom.congr_fun (augmentation_comp R σ C T I p δ hp l) c
  rw [hc, sub_self]
  exact I.zero_mem

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal
