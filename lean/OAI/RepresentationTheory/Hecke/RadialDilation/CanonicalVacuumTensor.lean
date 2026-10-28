import OAI.RepresentationTheory.Hecke.RadialDilation.Canonical
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor
import OAI.RepresentationTheory.Hecke.RadialDilation.LinearCoordinateProjection

/-! # Canonical Vacuum Tensor -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization

noncomputable section

section

/-! The canonical radial unit-ball input is exactly the global integral lattice vector. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] (μ : Place)

omit [Fintype Place] in
theorem finiteBlockProjection_apply (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) (i : Fin 3) :
    FiniteBlockChart.Realization.finiteBlockProjection q μ x i = FiniteSchur.Realization.finitePadicProjection q (x (μ, i)) :=
  LinearCoordinateProjection.Realization.linear_coordinate_projection_apply (FiniteSchur.Realization.finitePadicProjection q).toLinearMap (fun i : Fin 3 => (μ, i)) x i

omit [Fintype Place] in
theorem finiteBlockProjection_integral (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) (hx : x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) :
    ∀ i, ‖FiniteBlockChart.Realization.finiteBlockProjection q μ x i‖ ≤ 1 := by
  intro i
  rw [finiteBlockProjection_apply]
  exact FiniteSchur.Realization.finitePadicProjection_integral_norm q (x (μ, i)) (hx (μ, i))

omit [Fintype Place] in
theorem finiteBlockInclusion_integral (x : Mem.Realization.Position q) (hx : ∀ i, ‖x i‖ ≤ 1) :
    FiniteBlockChart.Realization.finiteBlockInclusion q μ x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
  intro p
  rw [FiniteBlockChart.Realization.finiteBlockInclusion_apply]
  by_cases hp : p.1 = μ
  · rw [ite_eq_left hp]
    exact LocalCharacterConductor.Realization.finitePadicInclusion_integral q (x p.2) (hx p.2)
  · rw [ite_eq_right hp]
    exact Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem

omit [Fintype Place] in
theorem finiteBlockChart_integral_iff (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ↔ (∀ i, ‖FiniteBlockChart.Realization.finiteBlockProjection q μ x i‖ ≤ 1) ∧
      (FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
  constructor
  · intro hx
    have hp := finiteBlockProjection_integral q μ x hx
    refine ⟨hp, ?_⟩
    change x - FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x) ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
    exact Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.sub_mem hx (finiteBlockInclusion_integral q μ _ hp)
  · rintro ⟨hp, hy⟩
    have heq : FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x) +
        (FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val = x := by
      change FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x) +
        (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x)) = x
      abel
    rw [← heq]
    exact Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.add_mem (finiteBlockInclusion_integral q μ _ hp) hy

theorem canonicalFiniteRadialEmbedding_unit_ball :
    Canonical.Realization.canonicalFiniteRadialEmbedding q μ ⟨Mem.Realization.radialBall q 0, Mem.Realization.radialBall_mem q 0⟩ = Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply Subtype.ext
  funext x
  change Mem.Realization.radialBall q 0 (FiniteBlockChart.Realization.finiteBlockProjection q μ x) * Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val =
    Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x
  by_cases hx : x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
  · obtain ⟨hp, hy⟩ := (finiteBlockChart_integral_iff q μ x).mp hx
    rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem hx, Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem hy]
    simp [Mem.Realization.radialBall, hp]
  · rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hx]
    by_cases hp : ∀ i, ‖FiniteBlockChart.Realization.finiteBlockProjection q μ x i‖ ≤ 1
    · have hy : (FiniteBlockChart.Realization.finiteBlockChart q μ x).2.val ∉ Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors :=
        fun hy => hx ((finiteBlockChart_integral_iff q μ x).mpr ⟨hp, hy⟩)
      rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hy, mul_zero]
    · simp [Mem.Realization.radialBall, hp]

end

/-! A vacuum eigenphase of an auxiliary matrix is uniform on every canonical radial input. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)

omit [DecidableEq Place] in
theorem canonicalFiniteRadialEmbedding_tensor (b : Cm.radialInput q) :
    Canonical.Realization.canonicalFiniteRadialEmbedding q μ b =
      FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest (TensorAction.Realization.radialTest q b) (Canonical.Realization.finiteAwayVacuum q μ)) :=
  TensorAction.Realization.finiteRadialEmbedding_tensor q (FiniteBlockChart.Realization.finiteBlockChart q μ) (Canonical.Realization.finiteAwayVacuum q μ).val
    (Canonical.Realization.finiteAwayVacuum q μ).property.1 (Canonical.Realization.finiteAwayVacuum q μ).property.2 b

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem auxiliary_vacuum_phase_uniform_radial (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
    (m : MpF)
    (hfix : ∀ p s : Mem.Realization.Position q,
      (D.finite.project m).val *ᵥ Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s))
    (ξ : ℂ) (hξ : D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction) :
    ∀ b : Cm.radialInput q,
      D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) = ξ • Canonical.Realization.canonicalFiniteRadialEmbedding q μ b := by
  obtain ⟨V, hV⟩ := FiniteAuxiliaryAction.Realization.finiteWeil_auxiliary_action q μ D m hfix
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  let f₀ := PadicTensorCommutant.Realization.padicVacuumTest q
  let φ := Canonical.Realization.finiteAwayVacuum q μ
  have hE₀ : E (TensorCommutant.Realization.tensorTest f₀ φ) = Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction :=
    (canonicalFiniteRadialEmbedding_tensor q μ ⟨Mem.Realization.radialBall q 0, Mem.Realization.radialBall_mem q 0⟩).symm.trans
      (canonicalFiniteRadialEmbedding_unit_ball q μ)
  have ht : TensorCommutant.Realization.tensorTest f₀ (V φ) = ξ • TensorCommutant.Realization.tensorTest f₀ φ := by
    apply E.injective
    rw [map_smul, hE₀]
    exact (hV f₀ φ).symm.trans (by rw [hE₀, hξ])
  have hφ : V φ = ξ • φ := by
    have h := congrArg (TensorCommutant.Realization.testRightSection (0 : Mem.Realization.Position q)) ht
    rw [map_smul, TensorCommutant.Realization.testRightSection_tensor, TensorCommutant.Realization.testRightSection_tensor,
      show f₀.val 0 = 1 from PadicTensorCommutant.Realization.padicVacuumTest_zero q, one_smul, one_smul] at h
    exact h
  intro b
  rw [canonicalFiniteRadialEmbedding_tensor, hV, hφ]
  change E (TensorCommutant.Realization.tensorLeftLinear (TensorAction.Realization.radialTest q b) (ξ • φ)) = ξ • E (TensorCommutant.Realization.tensorLeftLinear (TensorAction.Realization.radialTest q b) φ)
  rw [map_smul, map_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization
