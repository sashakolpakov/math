import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Indexed Prime Heisenberg -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeHeisenberg.Realization

noncomputable section

/-! Heisenberg tensor factorization with arbitrary finite global coordinate labels. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem indexedAwayHeisenberg_mem (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (p s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) (f : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) :
    PrimeHeisenberg.Realization.awayHeisenbergFunction q D p s f.val ∈ TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) := by
  constructor
  · apply IsLocallyConstant.mul
    · apply (FiniteSchur.Realization.finiteCharacter_locallyConstant D).comp_continuous
      unfold dotProduct
      fun_prop
    · exact f.property.1.comp_continuous (continuous_id.sub continuous_const)
  · exact (f.property.2.comp_homeomorph (Homeomorph.subRight s)).mul_left

def indexedAwayHeisenbergOperator (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (p s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) :
    TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) →ₗ[ℂ]
      TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I)) where
  toFun f := ⟨PrimeHeisenberg.Realization.awayHeisenbergFunction q D p s f.val, indexedAwayHeisenberg_mem q D p s f⟩
  map_add' f h := by apply Subtype.ext; funext y; exact mul_add _ _ _
  map_smul' c f := by apply Subtype.ext; funext y; exact mul_left_comm _ _ _

theorem indexedPrime_heisenberg_tensor {n : ℕ} (e : I ≃ Fin n) (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := I))) :
    FiniteSchur.Realization.finiteHeisenbergOperator D p s (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h) =
      IndexedPrimeChart.Realization.indexedPrimeTensor q e
        (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (FiniteSchur.Realization.finiteLocalCharacter q D)
          (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
          (Sum.elim (IndexedPrimeChart.Realization.indexedPrimeProjection q e s) (IndexedPrimeChart.Realization.indexedPrimeProjection q e p)) f)
        (indexedAwayHeisenbergOperator q D (PrimeChart.Realization.fullPrimeAway q p) (PrimeChart.Realization.fullPrimeAway q s) h) := by
  apply Subtype.ext
  funext x
  have hfun : (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h).val =
      fun z => f.val (IndexedPrimeChart.Realization.indexedPrimeProjection q e z) * h.val (PrimeChart.Realization.fullPrimeAway q z) :=
    funext (IndexedPrimeChart.Realization.indexedPrimeTensor_apply q e f h)
  change Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p s (IndexedPrimeChart.Realization.indexedPrimeTensor q e f h).val x = _
  rw [hfun, IndexedPrimeChart.Realization.indexedPrime_heisenberg_function, IndexedPrimeChart.Realization.indexedPrimeTensor_apply,
    PrimeHeisenberg.Realization.padic_heisenberg_coordinate_convention]
  rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeHeisenberg.Realization
