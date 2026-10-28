import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeHeisenberg
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Indexed Prime Bare Lift -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization

noncomputable section

section

/-! Actual local oscillators extend to the finite-adelic test space for any finite coordinate index. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (e : I ≃ Fin n)
local instance c410IndexedPrimeIntertwiner_measurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410IndexedPrimeIntertwiner_borel : BorelSpace ℚ_[q] := ⟨rfl⟩
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem indexedPrime_oscillator_local_covariance (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    u.val.2 (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (FiniteSchur.Realization.finiteLocalCharacter q D)
      (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v f) =
      Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (u.val.1.val *ᵥ v) (u.val.2 f) := by
  apply Subtype.ext
  exact (u.property.2 v f (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator
    (FiniteSchur.Realization.finiteLocalCharacter q D) (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v f)).mp rfl

theorem indexedPrime_oscillator_operator_covariance (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2).toLinearMap.comp (FiniteSchur.Realization.finiteHeisenbergOperator D p s) =
      (FiniteSchur.Realization.finiteHeisenbergOperator D (IndexedPrimePhaseAction.Realization.indexedPrimeMomentum q e u.val.1 p s)
        (IndexedPrimePhaseAction.Realization.indexedPrimePosition q e u.val.1 p s)).comp (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2).toLinearMap := by
  apply IndexedPrimeChart.Realization.indexedPrimeTensor_linear_ext q e
  intro f h
  change IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2 (FiniteSchur.Realization.finiteHeisenbergOperator D p s (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h)) =
    FiniteSchur.Realization.finiteHeisenbergOperator D (IndexedPrimePhaseAction.Realization.indexedPrimeMomentum q e u.val.1 p s) (IndexedPrimePhaseAction.Realization.indexedPrimePosition q e u.val.1 p s)
      (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2 (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h))
  rw [IndexedPrimeHeisenberg.Realization.indexedPrime_heisenberg_tensor, IndexedPrimeChart.Realization.indexedPrimeOperatorHom_tensor, IndexedPrimeChart.Realization.indexedPrimeOperatorHom_tensor,
    IndexedPrimeHeisenberg.Realization.indexedPrime_heisenberg_tensor, IndexedPrimePhaseAction.Realization.indexedPrime_transformed_away_momentum, IndexedPrimePhaseAction.Realization.indexedPrime_transformed_away_position,
    IndexedPrimePhaseAction.Realization.indexedPrime_transformed_localPhase, indexedPrime_oscillator_local_covariance]

theorem indexedPrime_oscillator_intertwines (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) :
    Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
      (IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e u.val.1) (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2) := by
  intro p s f h hh x
  have he : h = FiniteSchur.Realization.finiteHeisenbergOperator D p s f := Subtype.ext (funext hh)
  rw [he]
  exact congrArg (fun a : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => a.val x)
    (LinearMap.congr_fun (indexedPrime_oscillator_operator_covariance q e D u p s) f)

end

/-! Exact local bare-cover lifts for arbitrary finite global coordinate labels. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (e : I ≃ Fin n)
local instance c410IndexedPrimeBareLift_measurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410IndexedPrimeBareLift_borel : BorelSpace ℚ_[q] := ⟨rfl⟩
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def indexedPrimeOscillatorPair (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) :
    Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) →*
      (Theta.PoissonAutomorphyNormalizationData.Sp I Theta.PoissonAutomorphyNormalizationData.AQf × (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) where
  toFun u := (IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e u.val.1, IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e u.val.2)
  map_one' := Prod.ext (IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e).map_one (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e).map_one
  map_mul' u v := Prod.ext ((IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e).map_mul u.val.1 v.val.1)
    ((IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e).map_mul u.val.2 v.val.2)

theorem indexedPrimeOscillatorPair_minus (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) :
    indexedPrimeOscillatorPair q e D (Weil.Local.FunctionsMetaplectic.Construction.oscillatorMinus ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) =
      (1, LinearEquiv.neg ℂ) :=
  Prod.ext (IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e).map_one (IndexedPrimeChart.Realization.indexedPrimeOperatorHom_neg q e)

def indexedPrimeMetaplecticLift (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) :
    Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) →* MpF :=
  FiniteSchur.Realization.finiteBareLift D (Weil.Local.FunctionsMetaplectic.Construction.oscillatorMinus ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D))
    (indexedPrimeOscillatorPair q e D) (indexedPrime_oscillator_intertwines q e D)
    (indexedPrimeOscillatorPair_minus q e D)

theorem indexedPrimeMetaplecticLift_spec (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) :
    D.finite.project (indexedPrimeMetaplecticLift q e D u) =
      IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u) ∧
    D.finite.action (indexedPrimeMetaplecticLift q e D u) =
      IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u) := by
  have h := FiniteSchur.Realization.finiteBareLift_spec D (Weil.Local.FunctionsMetaplectic.Construction.oscillatorMinus ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D))
    (indexedPrimeOscillatorPair q e D) (indexedPrime_oscillator_intertwines q e D)
    (indexedPrimeOscillatorPair_minus q e D) u
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem indexedPrimeMetaplecticLift_tensor (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D))
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) :
    D.finite.action (indexedPrimeMetaplecticLift q e D u) (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h) =
      IndexedPrimeChart.Realization.indexedPrimeTensor q e (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u f) h := by
  rw [(indexedPrimeMetaplecticLift_spec q e D u).2, IndexedPrimeChart.Realization.indexedPrimeOperatorHom_tensor]

theorem every_indexedPrime_lift_tensor (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) (m : MpF)
    (hm : D.finite.project m = IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
      (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u)) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
      (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))),
      D.finite.action m (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h) =
        ε • IndexedPrimeChart.Realization.indexedPrimeTensor q e (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u f) h := by
  obtain ⟨ε, hε, ha⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m (indexedPrimeMetaplecticLift q e D u)
    (hm.trans (indexedPrimeMetaplecticLift_spec q e D u).1.symm)
  refine ⟨ε, hε, ?_⟩
  intro f h
  rw [ha, indexedPrimeMetaplecticLift_tensor]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization
