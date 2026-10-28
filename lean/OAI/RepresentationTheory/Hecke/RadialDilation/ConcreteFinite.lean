import OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalFactorization

/-! # Concrete Finite -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization

noncomputable section

section

/-! An actual rational Weil action realizes the radial dilation after a positive power. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem actual_rational_radial_power
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
    (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R)
    (M : ℕ) (hM : 0 < M)
    (hactive : ‖((a μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (N : ℕ) (s : MpF) (ξ : ℂ),
      0 < N ∧ 0 < N * M ∧ D.finite.project s = FiniteConjugation.Realization.finitePadicSymplecticInclusion q S ∧ ξ ^ 8 = 1 ∧
      ∀ b : Cm.radialInput q,
        D.finiteAction (γ ^ N) (D.finite.action s⁻¹ (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)) =
          ξ • D.finite.action s⁻¹ (Canonical.Realization.canonicalFiniteRadialEmbedding q μ
            (Mem.Realization.normalizedScalarSubstitution q (((a μ)⁻¹) ^ N : ℚ_[q]ˣ).val (N * M)
              (ScalarPowerFactorization.Realization.padic_scalar_norm_power q (a μ)⁻¹ M N hactive) b)) := by
  obtain ⟨N, hN, haux⟩ := AuxiliaryScalarStabilization.Realization.exists_scalar_auxiliary_power_radial_phase q μ hLocalWeil D S γ a hscalar ha haway
  obtain ⟨s, hs⟩ := FiniteConjugation.Realization.exists_finite_coordinate_lift q D S
  obtain ⟨u, hu⟩ := D.finite.surjective (ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (((a μ)⁻¹) ^ N))
  obtain ⟨α, hα, huact⟩ := ActiveFinitePhase.Realization.every_active_finite_lift_radial_phase q μ hLocalWeil D (((a μ)⁻¹) ^ N) (N * M)
    (ScalarPowerFactorization.Realization.padic_scalar_norm_power q (a μ)⁻¹ M N hactive) u hu
  obtain ⟨v, hv⟩ := D.finite.surjective (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a ^ N)
  obtain ⟨β, hβ, hvact⟩ := haux v hv
  let m := s * D.finiteLift (γ ^ N) * s⁻¹
  have hm : D.finite.project m = D.finite.project (u * v) := by
    rw [D.finite.project.map_mul u v, hu, hv, ScalarPowerFactorization.Realization.scalar_active_auxiliary_power_factorization q μ S γ a hscalar]
    change D.finite.project (s * D.finiteLift (γ ^ N) * s⁻¹) = AuxiliaryScalarMatrix.Realization.scalarFiniteConjugate q S (γ ^ N)
    rw [map_mul, map_mul, map_inv, hs, D.finiteLift_covers]
    rfl
  obtain ⟨ε, hε, he⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m (u * v) hm
  have hε8 : ε ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
  refine ⟨N, s, ε * (β * α), hN, Nat.mul_pos hN hM, hs, ?_, ?_⟩
  · rw [mul_pow, mul_pow, hε8, hα, hβ, one_mul, one_mul]
  · intro b
    apply RationalFactorization.Realization.finiteAction_undo_coordinates D s (γ ^ N)
    change D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) = _
    rw [he, map_mul]
    change ε • D.finite.action u (D.finite.action v (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)) = _
    rw [hvact, map_smul, huact, smul_smul, smul_smul]
    simp only [mul_assoc, Nat.cast_mul]

end

/-! Concrete injective input maps and the natural finite hypotheses of RadialDilation. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def coordinateRadialEmbedding (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (s : MpF) :
    Cm.radialInput q →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  (D.finite.action s⁻¹).toLinearMap.comp (Canonical.Realization.canonicalFiniteRadialEmbedding q μ)

theorem coordinateRadialEmbedding_injective (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (s : MpF) :
    Function.Injective (coordinateRadialEmbedding q μ D s) :=
  (D.finite.action s⁻¹).injective.comp (Canonical.Realization.canonicalFiniteRadialEmbedding_injective q μ)

theorem actual_finite_radial_inputs
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
    (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R)
    (M : ℕ) (hM : 0 < M)
    (hactive : ‖((a μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (N : ℕ) (s : MpF) (Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q) (ξ : ℂ),
      0 < N ∧ 0 < N * M ∧ D.finite.project s = FiniteConjugation.Realization.finitePadicSymplecticInclusion q S ∧
      Function.Injective (coordinateRadialEmbedding q μ D s) ∧ Cm.finitePhase ξ ∧
      (∀ (b : Cm.radialInput q) (x : Mem.Realization.Position q), (Uq b).val x =
        (Real.rpow (q : ℝ) (3 * ((N * M : ℕ) : ℝ) / 2) : ℂ) *
          b.val (fun i => ((q : ℚ_[q]) ^ (N * M))⁻¹ * x i)) ∧
      (∀ b : Cm.radialInput q,
        D.finiteAction (γ ^ N) (coordinateRadialEmbedding q μ D s b) =
          ξ • coordinateRadialEmbedding q μ D s (Uq b)) := by
  obtain ⟨N, s, ξ, hN, hNM, hs, hξ, hop⟩ := actual_rational_radial_power q μ hLocalWeil D S γ a
    hscalar ha haway M hM hactive
  let Uq := Mem.Realization.normalizedScalarSubstitution q (((a μ)⁻¹) ^ N : ℚ_[q]ˣ).val (N * M)
    (ScalarPowerFactorization.Realization.padic_scalar_norm_power q (a μ)⁻¹ M N hactive)
  refine ⟨N, s, Uq, ξ, hN, hNM, hs, coordinateRadialEmbedding_injective q μ D s,
    ⟨8, by decide, hξ⟩, ?_, hop⟩
  intro b x
  exact Mem.Realization.normalizedScalarSubstitution_apply q _ (N * M) _ b x

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization
