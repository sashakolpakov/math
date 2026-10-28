import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalCovers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators

/-! # Principal Column Bounds -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnBounds.CM

noncomputable section

/-! ThetaCycle: a deep principal congruence gives a literal common integer
multiple of the original lattice in every matrix column difference. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K)

theorem ball_lattice_standard_basis_denominator :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ j : Fin 3, d • (Pi.single j (1 : K)) ∈ B.lattice :=
  AbelianModuli.ReferenceFamily.LatticeDenominators.common_integer_multiple_mem B.lattice B.lattice_full (fun j => Pi.single j 1)

theorem principal_column_difference (d m k : ℤ) (hd : d ≠ 0)
    (hb : ∀ j : Fin 3, d • (Pi.single j (1 : K)) ∈ B.lattice)
    (N : ℕ) (hN : (N : ℤ) = d * m * k)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g) (j : Fin 3) :
    ∃ y ∈ B.lattice, g (Pi.single j 1) - Pi.single j 1 = m • y := by
  obtain ⟨y, hy, he⟩ := hg.2.2.2 (d • Pi.single j 1) (hb j)
  have hmap : g (d • Pi.single j 1) = d • g (Pi.single j 1) := map_zsmul g _ _
  refine ⟨k • y, B.lattice.smul_mem k hy, ?_⟩
  apply smul_right_injective (HeckeCycles.GeometricSource.CM.Vec K) (show (d : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hd)
  simp only [Int.cast_smul_eq_zsmul]
  rw [smul_sub, ← hmap, he, hN, mul_smul, mul_smul]

theorem principal_level_symm (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g) :
    B.principalLevel N g.symm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simpa only [g.apply_symm_apply] using (hg.1 (g.symm x) (g.symm y)).symm
  · have he := LinearEquiv.det_coe_symm g
    rw [hg.2.1, inv_one] at he
    exact he
  · intro x
    simpa only [g.apply_symm_apply] using (hg.2.2.1 (g.symm x)).symm
  · intro x hx
    have hx' : g.symm x ∈ B.lattice := (hg.2.2.1 (g.symm x)).mpr
      (by simpa only [g.apply_symm_apply] using hx)
    obtain ⟨y, hy, he⟩ := hg.2.2.2 (g.symm x) hx'
    refine ⟨-y, B.lattice.neg_mem hy, ?_⟩
    rw [g.apply_symm_apply] at he
    rw [smul_neg, ← he]
    abel

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnBounds.CM
