import OAI.Analysis.HodgeTheory.Decomposition.ContractionAlgebra

/-! # Bivector Contraction -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BivectorContraction.Constructions

noncomputable section

/-! Finite bivector contraction and its commutator with exterior
multiplication, in the normalization of the actual de Rham differential. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem exteriorContraction_sum_vector (n : ℕ) (u : ι → E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n (∑ i, u i) a = ∑ i, SymbolDifferential.Constructions.exteriorContraction n (u i) a :=
  map_sum a.curryLeft u Finset.univ

omit [Fintype ι] in
theorem exteriorContraction_sub_vector (n : ℕ) (u v : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n (u - v) a = SymbolDifferential.Constructions.exteriorContraction n u a - SymbolDifferential.Constructions.exteriorContraction n v a :=
  a.curryLeft.map_sub u v

def bivectorContraction (n : ℕ) (u v : ι → E) : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  ∑ i, (SymbolDifferential.Constructions.exteriorContraction n (v i)).comp (SymbolDifferential.Constructions.exteriorContraction (n + 1) (u i))

theorem bivectorContraction_apply (n : ℕ) (u v : ι → E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    bivectorContraction n u v a = ∑ i, SymbolDifferential.Constructions.exteriorContraction n (v i) (SymbolDifferential.Constructions.exteriorContraction (n + 1) (u i) a) := by
  simp only [bivectorContraction, sum_apply, ContinuousLinearMap.comp_apply]

theorem bivectorContraction_symbol_zero (ξ : E →L[ℝ] ℝ) (u v : ι → E) (a : DifferentialForms.Manifold.Basic.FormValue E 1) :
    bivectorContraction 0 u v (SymbolDifferential.Constructions.exteriorDifferentialSymbol 1 ξ a) =
      SymbolDifferential.Constructions.exteriorContraction 0 (∑ i, (ξ (u i) • v i - ξ (v i) • u i)) a := by
  rw [bivectorContraction_apply, exteriorContraction_sum_vector]
  apply Finset.sum_congr rfl
  intro i _
  rw [exteriorContraction_sub_vector, ContractionAlgebra.Constructions.exteriorContraction_smul_vector, ContractionAlgebra.Constructions.exteriorContraction_smul_vector]
  exact ContractionAlgebra.Constructions.exteriorDoubleContraction_symbol_zero ξ (u i) (v i) a

theorem bivectorContraction_symbol (n : ℕ) (ξ : E →L[ℝ] ℝ) (u v : ι → E)
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    bivectorContraction (n + 1) u v (SymbolDifferential.Constructions.exteriorDifferentialSymbol (n + 1 + 1) ξ a) -
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (bivectorContraction n u v a) =
        SymbolDifferential.Constructions.exteriorContraction (n + 1) (∑ i, (ξ (u i) • v i - ξ (v i) • u i)) a := by
  rw [bivectorContraction_apply, bivectorContraction_apply, map_sum,
    ← Finset.sum_sub_distrib, exteriorContraction_sum_vector]
  apply Finset.sum_congr rfl
  intro i _
  rw [exteriorContraction_sub_vector, ContractionAlgebra.Constructions.exteriorContraction_smul_vector, ContractionAlgebra.Constructions.exteriorContraction_smul_vector]
  exact ContractionAlgebra.Constructions.exteriorDoubleContraction_symbol n ξ (u i) (v i) a

end

end OAI.Analysis.HodgeTheory.Decomposition.BivectorContraction.Constructions
