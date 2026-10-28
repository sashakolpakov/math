import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticCoefficientMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators

/-! # Lattice Coefficient Bounds -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LatticeCoefficientBounds.CM

noncomputable section

/-! ThetaCycle: clear one common integer denominator for both actual quadratic
coefficients of the specified ball lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem ball_lattice_quadratic_coefficients_integral (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ B.lattice, ∀ (s : Fin 2) (i : Fin 3),
      IsIntegral ℤ (n • QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 s (x i)) := by
  have hs (s : Fin 2) := AbelianModuli.ReferenceFamily.LatticeDenominators.common_integral_coordinate_multiple
    (B.lattice.map ((QuadraticCoefficientMaps.CM.cmLatticeCoefficients K δ hδ hδ0 s).restrictScalars ℤ))
    (B.lattice_fg.map _)
  choose n hn hi using hs
  refine ⟨∏ s, n s, Finset.prod_ne_zero_iff.mpr (fun s _ => hn s), ?_⟩
  intro x hx s i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ s)
  rw [hc, mul_smul, smul_comm]
  exact (hi s (QuadraticCoefficientMaps.CM.cmLatticeCoefficients K δ hδ hδ0 s x)
    (Submodule.mem_map.mpr ⟨x, hx, rfl⟩) i).smul c

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LatticeCoefficientBounds.CM
