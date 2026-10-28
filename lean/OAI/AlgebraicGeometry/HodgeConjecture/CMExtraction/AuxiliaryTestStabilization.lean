import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTestStabilization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialHecke
import OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization

/-! # Auxiliary Test Stabilization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryTestStabilization.Local

noncomputable section

/-! Bounded auxiliary symplectic powers stabilize an arbitrary auxiliary
test with one finite phase, uniformly for the whole radial family. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization.Realization

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  (μ : Place) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ))
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem auxiliary_test_phase_uniform_radial (m : MpF)
    (hfix : ∀ p s : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.finite.project m).val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s))
    (ξ : ℂ) (hξ : D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ (Radial.Cyclicity.ball q 0)) =
      ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ (Radial.Cyclicity.ball q 0)) :
    ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
      D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) =
        ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b := by
  obtain ⟨V, hV⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteAuxiliaryAction.Realization.finiteWeil_auxiliary_action q μ D m hfix
  let E := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ)
  have hEmb (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) : AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b =
      E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ) := RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.finiteRadialEmbedding_tensor q _ _ _ _ b
  have ht : RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Radial.Cyclicity.ball q 0)) (V φ) =
      ξ • RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Radial.Cyclicity.ball q 0)) φ := by
    apply E.injective
    rw [map_smul, ← hV, ← hEmb, hξ, hEmb]
  have hφ : V φ = ξ • φ := by
    have h := congrArg (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (0 : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q)) ht
    have h0 : (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Radial.Cyclicity.ball q 0)).val 0 = 1 := by
      simp [RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest, Radial.Cyclicity.ball, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall]
    rwa [map_smul, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection_tensor, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection_tensor, h0, one_smul, one_smul] at h
  intro b
  rw [hEmb, hV, hφ]
  change E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorLeftLinear (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) (ξ • φ)) = ξ • E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorLeftLinear (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ)
  rw [map_smul, map_smul]

theorem exists_auxiliary_power_test_radial_phase
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ)
    (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) g =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ))
    (hbounded : ∀ (p : ℕ) [Fact p.Prime], ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom g) ^ N).val i j‖ ≤ R)
    (hfix : ∀ p s : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      g.val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF, D.finite.project m = g ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) =
          ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b := by
  let : Nonempty (Place × Fin 3) := ⟨(μ, 0)⟩
  obtain ⟨N, hN, hphase⟩ := AdelicTestStabilization.Local.exists_adelic_power_test_phase hLocalWeil Fintype.card_pos D
    (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ (Radial.Cyclicity.ball q 0)) g γ S he hbounded
  refine ⟨N, hN, ?_⟩
  intro m hm
  obtain ⟨ξ, hξ, hf⟩ := hphase m hm
  refine ⟨ξ, hξ, auxiliary_test_phase_uniform_radial q μ φ D m ?_ ξ hf⟩
  intro p s
  rw [hm]
  exact RepresentationTheory.Hecke.RadialDilation.AuxiliaryStabilization.Realization.matrix_power_fixes_vector g _ (hfix p s) N

theorem exists_scalar_auxiliary_power_test_phase
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      RepresentationTheory.Hecke.RadialDilation.ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF,
      D.finite.project m = RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) =
          ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b := by
  apply exists_auxiliary_power_test_radial_phase q μ φ D hLocalWeil
    (RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a) γ {RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q}
  · intro v hv
    exact RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_other_place q μ S γ a v (by simpa only [Finset.mem_singleton] using hv)
  · exact RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization.Realization.scalarAuxiliaryMatrix_power_bounds q μ S γ a hscalar ha haway
  · exact RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization.Realization.scalarAuxiliaryMatrix_fixes_active q μ S γ a hscalar

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryTestStabilization.Local
