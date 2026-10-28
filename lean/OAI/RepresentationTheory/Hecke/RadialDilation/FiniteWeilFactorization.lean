import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner
import OAI.RepresentationTheory.Hecke.RadialDilation.PadicTensorCommutant
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Finite Weil Factorization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteWeilFactorization.Realization

noncomputable section

/-! Factorization of an actual finite Weil operator into its local and auxiliary actions. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

local instance c410FiniteWeilFactorization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410FiniteWeilFactorization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem finiteWeil_local_factorization (m : MpF)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D))
    (hproject : ∀ v, (D.finite.project m).val *ᵥ FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ v =
      FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction
        (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g) v)) :
    ∃ V : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ),
      ∀ f h, D.finite.action m (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f h)) =
        FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
          (TensorCommutant.Realization.tensorTest (PadicTensorCommutant.Realization.padicTestWeil q (FiniteSchur.Realization.finiteLocalCharacter q D) g f) (V h)) := by
  let ψ := FiniteSchur.Realization.finiteLocalCharacter q D
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  let U := TensorCommutant.Realization.conjugateLinearAut E.symm (D.finite.action m)
  let φ := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ g)
  obtain ⟨V, hV⟩ := TensorCommutant.Realization.tensor_intertwiner_factors
    (PadicTensorCommutant.Realization.padicTestHeisenberg q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D))
    (PadicTensorCommutant.Realization.padic_test_commutant_scalar q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
      (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) (FiniteSchur.Realization.finiteLocalCharacter_unitary q D))
    φ (PadicTensorCommutant.Realization.padicTestWeil q ψ g) (PadicTensorCommutant.Realization.padicTestWeil_intertwines q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) g)
    U (FiniteBlockIntertwiner.Realization.finiteWeil_block_transport q μ D m φ hproject)
    (PadicTensorCommutant.Realization.padicVacuumTest q) 0 (PadicTensorCommutant.Realization.padicVacuumTest_zero q)
  refine ⟨V, ?_⟩
  intro f h
  have ht := congrArg E (hV f h)
  change E (E.symm (D.finite.action m (E (TensorCommutant.Realization.tensorTest f h)))) =
    E (TensorCommutant.Realization.tensorTest (PadicTensorCommutant.Realization.padicTestWeil q ψ g f) (V h)) at ht
  rw [E.apply_symm_apply] at ht
  exact ht

theorem padicTestWeil_radial_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (a : ℚ_[q]ˣ) (M : ℕ) (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ)))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D))
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g = Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a)) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
      PadicTensorCommutant.Realization.padicTestWeil q (FiniteSchur.Realization.finiteLocalCharacter q D) g (TensorAction.Realization.radialTest q b) =
        ξ • TensorAction.Realization.radialTest q (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  obtain ⟨ξ, hξ, hU⟩ := LocalLiftChoice.Realization.every_local_lift_radial_substitution q hLocalWeil (FiniteSchur.Realization.finiteLocalCharacter q D)
    (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (FiniteSchur.Realization.finiteLocalCharacter_unitary q D)
    (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) a M ha g hg
  refine ⟨ξ, hξ, ?_⟩
  intro b
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3
  apply L.injective
  change L (L.symm (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g (L (TensorAction.Realization.radialTest q b)))) = _
  rw [L.apply_symm_apply, map_smul]
  exact hU b

/-- The complete radial substitution law for the actual finite Weil action,
with its auxiliary operator constructed rather than assumed. -/
theorem finiteWeil_radial_factorization
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (m : MpF) (a : ℚ_[q]ˣ) (M : ℕ) (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ)))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D))
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 (FiniteSchur.Realization.finiteLocalCharacter q D) g = Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a))
    (hproject : ∀ v, (D.finite.project m).val *ᵥ FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ v =
      FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a)) v)) :
    ∃ (ξ : ℂ) (V : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ)),
      ξ ^ 8 = 1 ∧ ∀ (b : Cm.radialInput q) h,
        D.finite.action m (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest (TensorAction.Realization.radialTest q b) h)) =
          ξ • FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
            (TensorCommutant.Realization.tensorTest (TensorAction.Realization.radialTest q (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b)) (V h)) := by
  obtain ⟨V, hV⟩ := finiteWeil_local_factorization q μ D m g (by simpa only [hg] using hproject)
  obtain ⟨ξ, hξ, hξb⟩ := padicTestWeil_radial_substitution q D hLocalWeil a M ha g hg
  refine ⟨ξ, V, hξ, ?_⟩
  intro b h
  rw [hV, hξb, TensorAction.Realization.tensorTest_smul_left, map_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteWeilFactorization.Realization
