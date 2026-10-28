import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate
import Mathlib.RingTheory.Derivation.Lie

/-! # Coordinate Derivations -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateDerivations

noncomputable section

/-! The original coordinate derivations on an etale polynomial chart commute. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations

universe u v

variable (R A : Type u) (ι : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
  [Algebra.FormallyEtale (MvPolynomial ι R) A]

theorem bracket (i j : ι) : ⁅AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι j⁆ = 0 := by
  classical
  apply AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.ext R A ι
  intro l
  simp only [Derivation.commutator_apply, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation_coordinate, Derivation.zero_apply]
  split_ifs <;> simp

theorem commute (i j : ι) : Function.Commute (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i) (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι j) := by
  intro x
  have h := congrArg (fun D : Derivation R A A => D x) (bracket R A ι i j)
  change AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι j x) - AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι j (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i x) = 0 at h
  exact sub_eq_zero.mp h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateDerivations
