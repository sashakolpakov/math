import Mathlib

/-! # Finite Covolume -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteCovolume

noncomputable section

/-! The finite-index step in the arithmetic closure argument.
An invariant probability measure on a countable transitive discrete quotient
forces that quotient to be finite. This is a measure-theoretic theorem; no
arithmetic density is assumed. -/

open scoped Classical Pointwise ENNReal
open Set _root_.MeasureTheory

theorem finite_of_transitive_invariant_probability
    (G X : Type*) [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [Nonempty X] [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ] : Finite X := by
  let x : X := Classical.choice inferInstance
  have heq : ∀ y : X, μ {y} = μ {x} := by
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    simpa only [Set.smul_set_singleton] using measure_smul μ g ({x} : Set X)
  have hsum : (∑' _ : X, μ {x}) = 1 := by
    have h := μ.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
    simpa only [Set.indicator_univ, heq, measure_univ] using h
  have hpos : μ {x} ≠ 0 := by
    intro hz
    simp only [hz, tsum_zero] at hsum
    exact zero_ne_one hsum
  by_contra hfin
  let : Infinite X := not_finite_iff_infinite.mp hfin
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hsum
  exact ENNReal.top_ne_one hsum

/-- An open subgroup with a finite invariant quotient probability measure
has finite index. Second countability makes the discrete quotient countable. -/
theorem finiteIndex_of_open_invariant_probability
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    (H : Subgroup G) (hopen : IsOpen (H : Set G))
    (μ : @Measure (G ⧸ H) (borel (G ⧸ H)))
    (hprob : @IsProbabilityMeasure (G ⧸ H) (borel (G ⧸ H)) μ)
    (hinv : @SMulInvariantMeasure G (G ⧸ H) _ (borel (G ⧸ H)) μ) :
    H.FiniteIndex := by
  let : MeasurableSpace (G ⧸ H) := borel (G ⧸ H)
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hopen
  let : Countable (G ⧸ H) := countable_of_Lindelof_of_discrete
  let : IsProbabilityMeasure μ := hprob
  let : SMulInvariantMeasure G (G ⧸ H) μ := hinv
  let : Finite (G ⧸ H) := finite_of_transitive_invariant_probability G (G ⧸ H) μ
  exact Subgroup.finiteIndex_of_finite_quotient

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteCovolume
