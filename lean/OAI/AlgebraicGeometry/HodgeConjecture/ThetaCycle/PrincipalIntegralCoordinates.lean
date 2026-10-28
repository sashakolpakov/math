import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LatticeCoefficientBounds
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnBounds
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallCoordinates

/-! # Principal Integral Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalIntegralCoordinates.CM

noncomputable section

/-! ThetaCycle: sufficiently deep principal congruences have globally integral
quadratic coefficients in every matrix column difference, with respect
to the original specified lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem principal_column_coefficients_integral (B : HeckeCycles.GeometricSource.CM.BallDatum K) (d a k : ℤ)
    (hd : d ≠ 0) (hb : ∀ j : Fin 3, d • (Pi.single j (1 : K)) ∈ B.lattice)
    (ha : ∀ x ∈ B.lattice, ∀ (s : Fin 2) (i : Fin 3),
      IsIntegral ℤ (a • QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 s (x i)))
    (N : ℕ) (hN : (N : ℤ) = d * a * k) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) (i j : Fin 3) (s : Fin 2) :
    IsIntegral ℤ (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 s
      (g (Pi.single j 1) i - (Pi.single j 1 : HeckeCycles.GeometricSource.CM.Vec K) i)) := by
  obtain ⟨y, hy, he⟩ := PrincipalColumnBounds.CM.principal_column_difference K B d a k hd hb N hN g hg j
  have hcoord : g (Pi.single j 1) i - (Pi.single j 1 : HeckeCycles.GeometricSource.CM.Vec K) i = a • y i := congrFun he i
  rw [hcoord, map_zsmul]
  exact ha y hy s i

theorem exists_principal_integral_coordinate_depth (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N → ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K), B.principalLevel N g →
      ∀ (i j : Fin 3) (s : Fin 2),
        IsIntegral ℤ (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 s
          (g (Pi.single j 1) i - (Pi.single j 1 : HeckeCycles.GeometricSource.CM.Vec K) i)) := by
  obtain ⟨d, hd, hb⟩ := PrincipalColumnBounds.CM.ball_lattice_standard_basis_denominator K B
  obtain ⟨a, ha0, ha⟩ := LatticeCoefficientBounds.CM.ball_lattice_quadratic_coefficients_integral K δ hδ hδ0 B
  refine ⟨(d * a).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hd ha0), ?_⟩
  intro N hN g hg i j s
  have hdiv : d * a ∣ (N : ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa only [Int.natAbs_natCast] using hN)
  obtain ⟨k, hk⟩ := hdiv
  exact principal_column_coefficients_integral K δ hδ hδ0 B d a k hd hb ha N hk g hg i j s

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalIntegralCoordinates.CM
