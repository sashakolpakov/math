import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedFixed
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Unramified Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTensor.Local

noncomputable section

/-! The actual auxiliary tensor retained by an integral, locally
unramified finite test, including its conjugated inverse-transpose action. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  (μ : Place)

def finiteTestAway (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :
    RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ) :=
  RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (0 : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) ((RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ)).symm φ)

omit [DecidableEq Place] in
theorem finiteTestAway_apply (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (y : RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ) : (finiteTestAway q μ φ).val y = φ.val y.val := by
  change φ.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm (0, y)) = φ.val y.val
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart_symm, map_zero, zero_add]

variable (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
  (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
  (N : ℕ) (hN : 0 < N) (hcop : q.Coprime N)
  (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
    ∀ x, φ.val (u + x) = φ.val x)

include hsupport hN hcop hperiod

omit [DecidableEq Place] in
theorem finite_test_auxiliary_tensor :
    φ = AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ (finiteTestAway q μ φ)
      ⟨RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q 0⟩ := by
  apply Subtype.ext
  funext x
  change φ.val x = RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0 (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
    (finiteTestAway q μ φ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  rw [finiteTestAway_apply]
  exact UnramifiedTest.Local.finite_test_unit_ball_factor q μ φ hsupport N hN hcop hperiod x

omit [DecidableEq Place] in
theorem finiteTestAway_ne_zero (hφ : φ ≠ 0) : finiteTestAway q μ φ ≠ 0 := by
  intro h
  apply hφ
  apply Subtype.ext
  funext x
  have hf := UnramifiedTest.Local.finite_test_unit_ball_factor q μ φ hsupport N hN hcop hperiod x
  rw [← finiteTestAway_apply q μ φ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2, h] at hf
  simpa using hf

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF)

theorem finite_test_coordinate_tensor :
    D.finite.action u⁻¹ φ = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q μ D u (finiteTestAway q μ φ)
      ⟨RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q 0⟩ :=
  congrArg (D.finite.action u⁻¹) (finite_test_auxiliary_tensor q μ φ hsupport N hN hcop hperiod)

theorem finite_test_coordinate_dual_fixed {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) :
    D.finite.action u⁻¹ φ ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (CoordinateDualHecke.Local.coordinateDualRepresentation q e μ D u) := by
  intro g hg
  change CoordinateLocalHecke.coordinateActiveRepresentation q e μ D u (Contragredient.Local.contragredient ℚ_[q] g)
    (D.finite.action u⁻¹ φ) = D.finite.action u⁻¹ φ
  rw [CoordinateLocalHecke.coordinateActive_action]
  change D.finite.action u⁻¹ (D.finite.action
    (ActiveLocalLift.activeFiniteLift q e μ D (Contragredient.Local.contragredient ℚ_[q] g)) φ) = _
  rw [UnramifiedFixed.Local.integral_test_active_fixed q e μ D φ hsupport N hN hcop hperiod
    (Contragredient.Local.contragredient ℚ_[q] g) ((Contragredient.Local.contragredient_integral_iff q g).mpr hg)]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnramifiedTensor.Local
