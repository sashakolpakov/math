import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalFiniteFamilyStabilization

/-! # Indexed Prime Power Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePowerStabilization.Realization

noncomputable section

/-! Compact local powers stabilize finite-adelic tests with arbitrary coordinate labels. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (e : I ≃ Fin n)
local instance c410IndexedPrimePowerStabilization_measurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410IndexedPrimePowerStabilization_borel : BorelSpace ℚ_[q] := ⟨rfl⟩

omit [DecidableEq I] in
theorem exists_indexedPrime_operator_power_fixed
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (C : Set (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n)) (hC : IsCompact C)
    (hg : ∀ N : ℕ, (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g) ^ N ∈ C) :
    ∃ N : ℕ, 0 < N ∧ IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N)) φ = φ := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (IndexedPrimeChart.Realization.indexedPrimeChart q e)
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  let F := E.symm φ
  let s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := I) → Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n := fun y => L (TestSections.Realization.testSection y F)
  have hfinite : (Set.range s).Finite := by
    apply ((TestSections.Realization.testSection_range_finite F).image L).subset
    rintro a ⟨y, rfl⟩
    exact ⟨TestSections.Realization.testSection y F, ⟨y, rfl⟩, rfl⟩
  let J := Set.range s
  let : Fintype J := hfinite.fintype
  obtain ⟨N, hN, hfix⟩ := LocalFiniteFamilyStabilization.Realization.exists_local_power_fixes_finite_family q n hLocalWeil hn ψ hψ hunit hnontrivial
    g (fun j : J => j.val) C hC hg
  have hs (y : PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) : Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N) (s y) = s y :=
    hfix ⟨s y, ⟨y, rfl⟩⟩
  have hprod : TensorCommutant.Realization.extendTestHom (TensorCommutant.Realization.conjugateLinearAut L.symm (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N))) F = F := by
    apply Subtype.ext
    funext p
    change (L.symm (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N) (s p.2))).val p.1 = F.val p
    rw [hs]
    rfl
  refine ⟨N, hN, ?_⟩
  change E (TensorCommutant.Realization.extendTestHom (TensorCommutant.Realization.conjugateLinearAut L.symm (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N))) F) = φ
  rw [hprod]
  exact E.apply_symm_apply φ

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem exists_indexedPrime_cover_power_sign
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D)) (m : MpF)
    (hm : D.finite.project m = IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
      (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) g))
    (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (C : Set (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n)) (hC : IsCompact C)
    (hg : ∀ N : ℕ, (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) g) ^ N ∈ C) :
    ∃ (N : ℕ) (ε : ℂ), 0 < N ∧ ε ^ 2 = 1 ∧ D.finite.action (m ^ N) φ = ε • φ := by
  obtain ⟨N, hN, hfix⟩ := exists_indexedPrime_operator_power_fixed q e hLocalWeil hn
    (FiniteSchur.Realization.finiteLocalCharacter q D) (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
    (FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D) g φ C hC hg
  have hp : D.finite.project (m ^ N) = D.finite.project (IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D (g ^ N)) := by
    rw [(IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (g ^ N)).1, map_pow, hm, map_pow, map_pow]
  obtain ⟨ε, hε, ha⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D (m ^ N) (IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D (g ^ N)) hp
  refine ⟨N, ε, hN, hε, ?_⟩
  rw [ha, (IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (g ^ N)).2, hfix]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePowerStabilization.Realization
