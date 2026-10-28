import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Indexed Prime Chart -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization

noncomputable section

/-! Local finite-dimensional test inputs for an arbitrary finite set of global coordinate labels. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] {n : ℕ} (e : I ≃ Fin n)

def indexedPrimeChart : (I → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ (Fin n → ℚ_[q]) × PrimeChart.Realization.FullPrimeAwayPosition q (ι := I) :=
  (PrimeChart.Realization.fullPrimeChart q).trans ((PositionReindex.Realization.positionReindex e).prodCongr (Homeomorph.refl _))

def indexedPrimeProjection (x : I → Theta.PoissonAutomorphyNormalizationData.AQf) : Fin n → ℚ_[q] :=
  PositionReindex.Realization.positionReindex e (PrimeChart.Realization.fullPrimeProjection q x)

def indexedPrimeTensor (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  FiniteLocalOperators.Realization.finiteProductTestEquiv (indexedPrimeChart q e)
    (TensorCommutant.Realization.tensorTest ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm f) h)

theorem indexedPrimeTensor_apply (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) (x : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (indexedPrimeTensor q e f h).val x = f.val (indexedPrimeProjection q e x) * h.val (PrimeChart.Realization.fullPrimeAway q x) :=
  TensorCommutant.Realization.tensorTest_apply ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm f) h (indexedPrimeProjection q e x) (PrimeChart.Realization.fullPrimeAway q x)

theorem indexedPrimeTensor_linear_ext (U V : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (h : ∀ f k, U (indexedPrimeTensor q e f k) = V (indexedPrimeTensor q e f k)) : U = V := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (indexedPrimeChart q e)
  have heq : U.comp E.toLinearMap = V.comp E.toLinearMap := by
    apply TensorCommutant.Realization.test_linear_ext
    intro f k
    have hf := h (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n f) k
    change U (E (TensorCommutant.Realization.tensorTest ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm
      (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n f)) k)) = _ at hf
    rw [LinearEquiv.symm_apply_apply] at hf
    exact hf
  apply LinearMap.ext
  intro f
  obtain ⟨a, rfl⟩ := E.surjective f
  exact LinearMap.congr_fun heq a

def indexedPrimeOperatorHom :
    (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) →* (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :=
  (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (indexedPrimeChart q e))).comp
    (TensorCommutant.Realization.extendTestHom.comp (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm))

theorem indexedPrimeOperatorHom_tensor (U : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) :
    indexedPrimeOperatorHom q e U (indexedPrimeTensor q e f h) = indexedPrimeTensor q e (U f) h := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (indexedPrimeChart q e)
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  change E (TensorCommutant.Realization.extendTestHom (TensorCommutant.Realization.conjugateLinearAut L.symm U)
    (E.symm (E (TensorCommutant.Realization.tensorTest (L.symm f) h)))) = E (TensorCommutant.Realization.tensorTest (L.symm (U f)) h)
  rw [E.symm_apply_apply, TensorCommutant.Realization.extendTestHom_tensor]
  change E (TensorCommutant.Realization.tensorTest (L.symm (U (L (L.symm f)))) h) = E (TensorCommutant.Realization.tensorTest (L.symm (U f)) h)
  rw [L.apply_symm_apply]

theorem indexedPrimeOperatorHom_neg : indexedPrimeOperatorHom q e (LinearEquiv.neg ℂ) = LinearEquiv.neg ℂ := by
  unfold indexedPrimeOperatorHom
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, TensorCommutant.Realization.conjugateLinearAut_neg,
    TensorCommutant.Realization.extendTestHom_neg, TensorCommutant.Realization.conjugateLinearAut_neg]

variable [DecidableEq I] {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem indexedPrime_heisenberg_function (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (p s x : I → Theta.PoissonAutomorphyNormalizationData.AQf) (f : (Fin n → ℚ_[q]) → ℂ) (h : PrimeChart.Realization.FullPrimeAwayPosition q (ι := I) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p s
      (fun z => f (indexedPrimeProjection q e z) * h (PrimeChart.Realization.fullPrimeAway q z)) x =
      Theta.PoissonAutomorphyNormalizationData.heisenberg (FiniteSchur.Realization.finiteLocalCharacter q D) (indexedPrimeProjection q e p) (indexedPrimeProjection q e s)
        f (indexedPrimeProjection q e x) *
      PrimeHeisenberg.Realization.awayHeisenbergFunction q D (PrimeChart.Realization.fullPrimeAway q p) (PrimeChart.Realization.fullPrimeAway q s) h (PrimeChart.Realization.fullPrimeAway q x) := by
  have h := PrimeHeisenberg.Realization.fullPrime_heisenberg_function q D p s x (fun z => f (PositionReindex.Realization.positionReindex e z)) h
  rw [← PositionReindex.Realization.heisenberg_positionReindex_forward] at h
  exact h

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization
