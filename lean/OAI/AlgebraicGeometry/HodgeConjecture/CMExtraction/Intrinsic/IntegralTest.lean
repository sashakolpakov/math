import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.IntegralScalar
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTensor

/-! # Integral Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralTest.Local

noncomputable section

/-! At a good integral coordinate prime, the same finite test is fixed
by the native conjugated local action and lies in an actual auxiliary
radial family. Its original theta value is preserved. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n) (hq : 2 < q)
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (u : MpF)
  (hu : D.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)
  (hS : ∀ i j, ‖S.val i j‖ ≤ 1)
  (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
  (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
  (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
  (hperiod : ∀ w ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
    ∀ x, φ.val (w + x) = φ.val x)

include e hLocalWeil hn hq hu hS hsupport hN hcop hperiod

theorem integral_coordinate_inverse_scalar :
    ∃ c : ℂ, c ≠ 0 ∧ D.finite.action u⁻¹ φ = c • φ := by
  have hui : D.finite.project u⁻¹ = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S⁻¹ := by
    rw [map_inv, hu, map_inv]
  exact Finite.IntegralScalar.Local.integral_finite_lift_test_scalar q e hLocalWeil hn hq D S⁻¹ u⁻¹ hui
    (PadicIntegralSymplectic.Local.padic_symplectic_inverse_integral q S hS) φ hsupport N hN hcop hperiod

theorem integral_coordinate_dual_fixed :
    φ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateDualHecke.Local.coordinateDualRepresentation q e μ D u) := by
  obtain ⟨c, hc, hscalar⟩ := integral_coordinate_inverse_scalar q e hLocalWeil hn hq D S u hu hS
    φ hsupport N hN hcop hperiod
  have hf := UnramifiedTensor.Local.finite_test_coordinate_dual_fixed q μ φ hsupport N hN hcop hperiod D u e
  intro g hg
  have h := hf g hg
  rw [hscalar, map_smul] at h
  have hh := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) => c⁻¹ • f) h
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

theorem integral_coordinate_radial_preimage (hφ : φ ≠ 0) :
    ∃ a : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ), a ≠ 0 ∧
      ∃ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q, AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q μ D u a b = φ := by
  obtain ⟨c, hc, hscalar⟩ := integral_coordinate_inverse_scalar q e hLocalWeil hn hq D S u hu hS
    φ hsupport N hN hcop hperiod
  let a := UnramifiedTensor.Local.finiteTestAway q μ φ
  let b₀ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := ⟨RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q 0⟩
  have hj : AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q μ D u a b₀ = c • φ :=
    (UnramifiedTensor.Local.finite_test_coordinate_tensor q μ φ hsupport N hN hcop hperiod D u).symm.trans hscalar
  refine ⟨a, UnramifiedTensor.Local.finiteTestAway_ne_zero q μ φ hsupport N hN hcop hperiod hφ, c⁻¹ • b₀, ?_⟩
  rw [map_smul, hj, smul_smul, inv_mul_cancel₀ hc, one_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralTest.Local
