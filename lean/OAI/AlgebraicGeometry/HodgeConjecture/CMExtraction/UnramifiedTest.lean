import OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor

/-! # Unramified Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTest.Local

noncomputable section

/-! An integral finite test with translation level N has the standard
unit-ball factor at every prime coprime to N. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] (μ : Place)

omit [Fintype Place] in
theorem finiteBlockInclusion_level (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hx : ∀ i, ‖x i‖ ≤ 1) :
    RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne') := by
  apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff _ _ _).mpr
  have he : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (N : ℚ)⁻¹ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ x) =
      RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ ((N : ℚ)⁻¹ • x) := by
    exact ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ).map_smul (N : ℚ)⁻¹ x).symm
  rw [he]
  apply RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization.finiteBlockInclusion_integral
  intro i
  have hn : ‖(N : ℚ_[q])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  simpa [Algebra.smul_def, norm_mul, hn] using hx i

theorem finite_test_unit_ball_factor
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x) (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    φ.val x = RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0 (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) * φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val := by
  by_cases hp : ∀ i, ‖RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x i‖ ≤ 1
  · have hi := finiteBlockInclusion_level q μ N hN hcop (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) hp
    have h := hperiod _ hi (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val
    have hd : RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) +
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val = x := by
      change RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) +
        (x - RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x)) = x
      abel
    rw [hd] at h
    simpa [RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall, hp] using h
  · have hi : x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := fun hx => hp (RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization.finiteBlockProjection_integral q μ x hx)
    rw [hsupport x hi]
    simp [RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall, hp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTest.Local
