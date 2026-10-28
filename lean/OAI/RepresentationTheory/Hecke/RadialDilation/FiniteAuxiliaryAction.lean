import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockHeisenberg
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Finite Auxiliary Action -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteAuxiliaryAction.Realization

noncomputable section

/-! Extract the actual auxiliary action from a finite Weil operator fixing the local phase block. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem finite_block_commutant_factors
    (U : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hU : ∀ p s f, U (FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p)
      (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) f) =
        FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) (U f)) :
    ∃ V : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ),
      ∀ f g, U (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f g)) =
        FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f (V g)) := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  let W := TensorCommutant.Realization.conjugateLinearAut E.symm U
  let ψ := FiniteSchur.Realization.finiteLocalCharacter q D
  have hW (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
      (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
      W (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) f) =
        TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) (W f) := by
    let p : Mem.Realization.Position q := fun i => v (Sum.inr i)
    let s : Mem.Realization.Position q := fun i => v (Sum.inl i)
    have hv : Sum.elim s p = v := by funext i; cases i <;> rfl
    have hcov (a : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
        FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) (E a) =
          E (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) a) := by
      simpa only [hv] using FiniteBlockHeisenberg.Realization.finiteBlock_heisenberg_operator q μ D p s a
    apply E.injective
    change E (E.symm (U (E (TensorCommutant.Realization.extendTestLinear _ f)))) = E (TensorCommutant.Realization.extendTestLinear _ (W f))
    rw [E.apply_symm_apply, ← hcov, hU, ← hcov]
    have hEW : E (W f) = U (E f) := E.apply_symm_apply _
    rw [hEW]
  obtain ⟨V, hV, _⟩ := TensorCommutant.Realization.local_commutant_equiv_factors
    (PadicTensorCommutant.Realization.padicTestHeisenberg q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D))
    (PadicTensorCommutant.Realization.padic_test_commutant_scalar q ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
      (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) (FiniteSchur.Realization.finiteLocalCharacter_unitary q D)) W hW
    (PadicTensorCommutant.Realization.padicVacuumTest q) 0 (PadicTensorCommutant.Realization.padicVacuumTest_zero q)
  refine ⟨V, ?_⟩
  intro f g
  have ht := congrArg (fun T => E (T (TensorCommutant.Realization.tensorTest f g))) hV
  change E (E.symm (U (E (TensorCommutant.Realization.tensorTest f g)))) = E (TensorCommutant.Realization.rightTestHom V (TensorCommutant.Realization.tensorTest f g)) at ht
  rw [E.apply_symm_apply, TensorCommutant.Realization.rightTestHom_tensor] at ht
  exact ht

theorem finiteWeil_commutes_local_block (m : MpF)
    (hfix : ∀ p s : Mem.Realization.Position q,
      (D.finite.project m).val *ᵥ Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) :
    ∀ p s f, D.finite.action m (FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p)
      (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) f) =
      FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
        (D.finite.action m f) := by
  intro p s f
  apply Subtype.ext
  funext x
  have h := D.finite.intertwines m (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) f
    (FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) f)
    (fun _ => rfl) x
  rw [hfix] at h
  exact h

/-- The only hypothesis is the action of the projected symplectic matrix on
the selected phase block; the auxiliary operator is constructed from the actual Weil action. -/
theorem finiteWeil_auxiliary_action (m : MpF)
    (hfix : ∀ p s : Mem.Realization.Position q,
      (D.finite.project m).val *ᵥ Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) :
    ∃ V : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ),
      ∀ f g, D.finite.action m (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f g)) =
        FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f (V g)) :=
  finite_block_commutant_factors q μ D (D.finite.action m)
    (finiteWeil_commutes_local_block q μ D m hfix)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteAuxiliaryAction.Realization
