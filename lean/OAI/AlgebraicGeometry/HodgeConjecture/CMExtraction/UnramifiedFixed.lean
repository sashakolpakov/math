import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

/-! # Unramified Fixed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedFixed.Local

noncomputable section

/-! Integral finite tests are fixed by the actual phase-free active
special-linear lift at primes coprime to their translation level. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem integral_test_active_fixed
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
      ∀ x, φ.val (u + x) = φ.val x)
    (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) φ = φ := by
  apply Subtype.ext
  funext x
  rw [ActiveLocalLift.activeFiniteLift_block_substitution]
  rw [UnramifiedTest.Local.finite_test_unit_ball_factor q μ φ hsupport N hN hcop hperiod]
  change RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0
      ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).1) *
      φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).2.val = _
  rw [Homeomorph.apply_symm_apply]
  have hb : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0 ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) =
      RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0 (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) := by
    simp only [RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall, neg_zero, zpow_zero,
      Radial.Hecke.integral_inverse_ball_iff q g hg 1 zero_le_one]
  rw [hb]
  exact (UnramifiedTest.Local.finite_test_unit_ball_factor q μ φ hsupport N hN hcop hperiod x).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedFixed.Local
