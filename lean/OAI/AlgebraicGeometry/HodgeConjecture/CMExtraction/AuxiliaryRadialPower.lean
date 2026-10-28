import OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalFactorization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryTestStabilization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryActivePhase

/-! # Auxiliary Radial Power -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialPower.Local

noncomputable section

/-! The actual rational Weil action dilates every radial family with an arbitrary auxiliary test, after a positive power and in the same fixed finite coordinates. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem actual_rational_auxiliary_radial_power
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
    (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ))
    (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (s : MpF) (hs : D.finite.project s = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)
    (hscalar : ∀ x, S.val *ᵥ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      RepresentationTheory.Hecke.RadialDilation.ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R)
    (M : ℕ) (hM : 0 < M)
    (hactive : ‖((a μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (N : ℕ) (ξ : ℂ),
      0 < N ∧ 0 < N * M ∧ ξ ^ 8 = 1 ∧
      ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        D.finiteAction (γ ^ N) (D.finite.action s⁻¹ (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b)) =
          ξ • D.finite.action s⁻¹ (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ
            (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution q (((a μ)⁻¹) ^ N : ℚ_[q]ˣ).val (N * M)
              (RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization.padic_scalar_norm_power q (a μ)⁻¹ M N hactive) b)) := by
  obtain ⟨N, hN, haux⟩ := AuxiliaryTestStabilization.Local.exists_scalar_auxiliary_power_test_phase q μ φ D hLocalWeil S γ a hscalar ha haway
  obtain ⟨u, hu⟩ := D.finite.surjective (RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (((a μ)⁻¹) ^ N))
  obtain ⟨α, hα, huact⟩ := AuxiliaryActivePhase.Local.every_active_finite_lift_auxiliary_phase q μ φ hLocalWeil D (((a μ)⁻¹) ^ N) (N * M)
    (RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization.padic_scalar_norm_power q (a μ)⁻¹ M N hactive) u hu
  obtain ⟨v, hv⟩ := D.finite.surjective (RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a ^ N)
  obtain ⟨β, hβ, hvact⟩ := haux v hv
  let m := s * D.finiteLift (γ ^ N) * s⁻¹
  have hm : D.finite.project m = D.finite.project (u * v) := by
    rw [D.finite.project.map_mul u v, hu, hv, RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization.scalar_active_auxiliary_power_factorization q μ S γ a hscalar]
    change D.finite.project (s * D.finiteLift (γ ^ N) * s⁻¹) = RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization.scalarFiniteConjugate q S (γ ^ N)
    rw [map_mul, map_mul, map_inv, hs, D.finiteLift_covers]
    rfl
  obtain ⟨ε, hε, he⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finite_lifts_differ_by_sign D m (u * v) hm
  have hε8 : ε ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
  refine ⟨N, ε * (β * α), hN, Nat.mul_pos hN hM, ?_, ?_⟩
  · rw [mul_pow, mul_pow, hε8, hα, hβ, one_mul, one_mul]
  · intro b
    apply RepresentationTheory.Hecke.RadialDilation.RationalFactorization.Realization.finiteAction_undo_coordinates D s (γ ^ N)
    change D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) = _
    rw [he, map_mul]
    change ε • D.finite.action u (D.finite.action v (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b)) = _
    rw [hvact, map_smul, huact, smul_smul, smul_smul]
    simp only [mul_assoc, Nat.cast_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialPower.Local
