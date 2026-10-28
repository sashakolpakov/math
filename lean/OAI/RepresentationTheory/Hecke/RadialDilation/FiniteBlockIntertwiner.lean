import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockHeisenberg

/-! # Finite Block Intertwiner -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization

noncomputable section

/-! Projected local phase actions give actual finite Weil intertwining identities. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def finiteBlockPhase (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) : Sum (Place × Fin 3) (Place × Fin 3) → Theta.PoissonAutomorphyNormalizationData.AQf :=
  Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i)))

def finiteBlockHeisenberg (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i)))

theorem finiteBlockHeisenberg_transport (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    finiteBlockHeisenberg q μ D v (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) f) =
      FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
        (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
          (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) f) := by
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  simpa only [finiteBlockHeisenberg, hv] using FiniteBlockHeisenberg.Realization.finiteBlock_heisenberg_operator q μ D
    (fun i => v (Sum.inr i)) (fun i => v (Sum.inl i)) f

theorem finiteWeil_block_intertwines (m : MpF) (φ : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3 → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (hproject : ∀ v, (D.finite.project m).val *ᵥ finiteBlockPhase q μ v = finiteBlockPhase q μ (φ v))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :
    D.finite.action m (finiteBlockHeisenberg q μ D v f) =
      finiteBlockHeisenberg q μ D (φ v) (D.finite.action m f) := by
  apply Subtype.ext
  funext x
  have h := D.finite.intertwines m
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i))) f (finiteBlockHeisenberg q μ D v f)
    (fun _ => rfl) x
  change (D.finite.action m (finiteBlockHeisenberg q μ D v f)).val x =
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
      (fun i => ((D.finite.project m).val *ᵥ finiteBlockPhase q μ v) (Sum.inl i))
      (fun i => ((D.finite.project m).val *ᵥ finiteBlockPhase q μ v) (Sum.inr i))
      (D.finite.action m f).val x at h
  rw [hproject] at h
  exact h

theorem finiteWeil_block_transport (m : MpF) (φ : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3 → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (hproject : ∀ v, (D.finite.project m).val *ᵥ finiteBlockPhase q μ v = finiteBlockPhase q μ (φ v))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)).symm (D.finite.action m)
      (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) f) =
    TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
      (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (φ v))
      (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)).symm (D.finite.action m) f) := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  let W := TensorCommutant.Realization.conjugateLinearAut E.symm (D.finite.action m)
  have hEW (a : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) : E (W a) = D.finite.action m (E a) :=
    E.apply_symm_apply _
  change W (TensorCommutant.Realization.extendTestLinear _ f) = TensorCommutant.Realization.extendTestLinear _ (W f)
  apply E.injective
  rw [hEW, ← finiteBlockHeisenberg_transport, finiteWeil_block_intertwines q μ D m φ hproject,
    ← finiteBlockHeisenberg_transport, hEW]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization
