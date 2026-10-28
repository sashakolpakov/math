import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart

/-! # Indexed Prime Substitution -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution.Realization

noncomputable section

/-! An actual local substitution acts by substitution in the full finite-prime chart. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] {n : ℕ} (e : I ≃ Fin n)

theorem indexedPrimeOperatorHom_substitution
    (U : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (c : ℂ) (T : (Fin n → ℚ_[q]) → (Fin n → ℚ_[q]))
    (hU : ∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n, ∀ x, (U f).val x = c * f.val (T x))
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (IndexedPrimeChart.Realization.indexedPrimeOperatorHom q e U f).val x =
      c * f.val ((IndexedPrimeChart.Realization.indexedPrimeChart q e).symm
        (T (IndexedPrimeChart.Realization.indexedPrimeProjection q e x), PrimeChart.Realization.fullPrimeAway q x)) := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (IndexedPrimeChart.Realization.indexedPrimeChart q e)
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  change (U (L (TestSections.Realization.testSection (PrimeChart.Realization.fullPrimeAway q x) (E.symm f)))).val
    (IndexedPrimeChart.Realization.indexedPrimeProjection q e x) = _
  rw [hU]
  rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution.Realization
