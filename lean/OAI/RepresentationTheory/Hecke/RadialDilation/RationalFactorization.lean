import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteScalarProjection
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteWeilFactorization

/-! # Rational Factorization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RationalFactorization.Realization

noncomputable section

/-! The actual rational finite action on radial inputs in a proved local coordinate chart. -/

open scoped Classical _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteAction_undo_coordinates (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (s : MpF) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (ξ : ℂ) (f h : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (htrans : D.finite.action (s * D.finiteLift γ * s⁻¹) f = ξ • h) :
    D.finiteAction γ (D.finite.action s⁻¹ f) = ξ • D.finite.action s⁻¹ h := by
  have hc (a : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : D.finite.action s⁻¹ (D.finite.action s a) = a := by
    change (D.finite.action s⁻¹ * D.finite.action s) a = a
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have ht := congrArg (D.finite.action s⁻¹) htrans
  rw [D.finite.action.map_mul, D.finite.action.map_mul, map_smul] at ht
  change D.finite.action s⁻¹ (D.finite.action s (D.finiteAction γ (D.finite.action s⁻¹ f))) = _ at ht
  rw [hc] at ht
  exact ht

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

local instance c410RationalRadialFactorization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410RationalRadialFactorization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem rational_finite_radial_factorization
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (M : ℕ) (ha : ‖((a μ)⁻¹ : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (s : MpF) (ξ : ℂ)
      (V : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ)),
      D.finite.project s = FiniteConjugation.Realization.finitePadicSymplecticInclusion q S ∧ ξ ^ 8 = 1 ∧
      ∀ (b : Cm.radialInput q) h,
        D.finiteAction γ (D.finite.action s⁻¹
          (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest (TensorAction.Realization.radialTest q b) h))) =
        ξ • D.finite.action s⁻¹ (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
          (TensorCommutant.Realization.tensorTest (TensorAction.Realization.radialTest q (Mem.Realization.normalizedScalarSubstitution q ((a μ)⁻¹ : ℚ_[q]ˣ).val M ha b)) (V h))) := by
  obtain ⟨s, hs⟩ := FiniteConjugation.Realization.exists_finite_coordinate_lift q D S
  obtain ⟨g, _, hg, _, _, _⟩ := LocalLiftChoice.Realization.localWeil_radial_substitution q hLocalWeil (FiniteSchur.Realization.finiteLocalCharacter q D)
    (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (FiniteSchur.Realization.finiteLocalCharacter_unitary q D)
    (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) (a μ)⁻¹ M ha
  obtain ⟨ξ, V, hξ, hV⟩ := FiniteWeilFactorization.Realization.finiteWeil_radial_factorization q μ D hLocalWeil
    (s * D.finiteLift γ * s⁻¹) (a μ)⁻¹ M ha g hg
    (FiniteScalarProjection.Realization.finite_coordinate_scalar_projection q μ D S s hs γ a hscalar)
  refine ⟨s, ξ, V, hs, hξ, ?_⟩
  intro b h
  exact finiteAction_undo_coordinates D s γ ξ _ _ (hV b h)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RationalFactorization.Realization
