import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteAuxiliaryAction

/-! # Canonical -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Canonical.Realization

noncomputable section

/-! A concrete nonzero auxiliary vacuum and its injective radial finite-adele input. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} (μ : Place)

theorem finiteAway_isClosed : IsClosed (FiniteBlockChart.Realization.FiniteAwayPosition q μ : Set (Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf)) :=
  isClosed_eq (FiniteBlockChart.Realization.finiteBlockProjection_continuous q μ) continuous_const

variable [Fintype Place]

def finiteAwayVacuum : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) := by
  let f := (FiniteLocalOperators.Realization.finiteTestSpaceEquiv (Place × Fin 3)).symm Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
  exact ⟨f.val ∘ Subtype.val, f.property.1.comp_continuous continuous_subtype_val,
    f.property.2.comp_isClosedEmbedding (finiteAway_isClosed q μ).isClosedEmbedding_subtypeVal⟩

theorem finiteAwayVacuum_zero : (finiteAwayVacuum q μ).val 0 = 1 :=
  Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem (Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem)

theorem finiteAwayVacuum_ne_zero : (finiteAwayVacuum q μ).val ≠ 0 := by
  intro h
  have hz := congrFun h 0
  rw [finiteAwayVacuum_zero] at hz
  exact one_ne_zero hz

def canonicalFiniteRadialEmbedding : Cm.radialInput q →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  FiniteTestEmbedding.Realization.finiteRadialEmbedding q (FiniteBlockChart.Realization.finiteBlockChart q μ) (finiteAwayVacuum q μ).val
    (finiteAwayVacuum q μ).property.1 (finiteAwayVacuum q μ).property.2

theorem canonicalFiniteRadialEmbedding_injective :
    Function.Injective (canonicalFiniteRadialEmbedding q μ) :=
  FiniteTestEmbedding.Realization.finiteRadialEmbedding_injective q (FiniteBlockChart.Realization.finiteBlockChart q μ) (finiteAwayVacuum q μ).val
    (finiteAwayVacuum q μ).property.1 (finiteAwayVacuum q μ).property.2
    (finiteAwayVacuum_ne_zero q μ)

variable [DecidableEq Place]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

local instance c410CanonicalRadialInput_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410CanonicalRadialInput_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem canonical_radial_local_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (a : ℚ_[q]ˣ) (M : ℕ) (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ)))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D))
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g =
      Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a)) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
      FiniteLocalOperators.Realization.finiteLocalOperatorHom q (FiniteBlockChart.Realization.finiteBlockChart q μ)
        (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g)
          (canonicalFiniteRadialEmbedding q μ b) =
        ξ • canonicalFiniteRadialEmbedding q μ
          (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) :=
  TensorAction.Realization.actual_radial_tensor_substitution q hLocalWeil (FiniteBlockChart.Realization.finiteBlockChart q μ) (finiteAwayVacuum q μ).val
    (finiteAwayVacuum q μ).property.1 (finiteAwayVacuum q μ).property.2
    (FiniteSchur.Realization.finiteLocalCharacter q D) (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
    (FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) a M ha g hg

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Canonical.Realization
