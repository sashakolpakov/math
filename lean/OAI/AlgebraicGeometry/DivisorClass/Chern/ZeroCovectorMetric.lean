import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric

/-! # Zero Covector Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroCovectorMetric

noncomputable section

/-! The original exterior-Gram metric in degree zero is the ordinary scalar Hermitian product. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions

theorem bilinearFormMetricPair_degree_zero {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 0 B a c = conj (a 0) * c 0 := by
  classical
  let s0 : Set.powersetCard ι 0 := ⟨∅, rfl⟩
  have hs (s : Set.powersetCard ι 0) : s = s0 :=
    Subtype.ext (Finset.card_eq_zero.mp s.property)
  let : Unique (Set.powersetCard ι 0) := ⟨⟨s0⟩, hs⟩
  have hB : Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b 0 B = 1 := by
    ext s t
    simp [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram, Matrix.one_apply, Subsingleton.elim s t]
  rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair, hB, inv_one]
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq, Complex.ofReal_one, mul_one]
  have hv : Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.basisExteriorTuple b 0 (default : Set.powersetCard ι 0) = 0 := Subsingleton.elim _ _
  rw [hv]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroCovectorMetric
