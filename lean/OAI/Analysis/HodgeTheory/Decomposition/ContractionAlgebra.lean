import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential

/-! # Contraction Algebra -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ContractionAlgebra.Constructions

noncomputable section

/-! Algebra of insertion operators and their exact commutator with
exterior multiplication, including the degree-one boundary case. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exteriorContraction_add_vector (n : ℕ) (u v : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n (u + v) a = SymbolDifferential.Constructions.exteriorContraction n u a + SymbolDifferential.Constructions.exteriorContraction n v a :=
  a.curryLeft.map_add u v

theorem exteriorContraction_smul_vector (n : ℕ) (r : ℝ) (u : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n (r • u) a = r • SymbolDifferential.Constructions.exteriorContraction n u a :=
  a.curryLeft.map_smul r u

theorem exteriorContraction_squared (n : ℕ) (u : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n u (SymbolDifferential.Constructions.exteriorContraction (n + 1) u a) = 0 := by
  exact ContinuousAlternatingMap.curryLeft_same a u

theorem exteriorContraction_anticommute (n : ℕ) (u v : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n u (SymbolDifferential.Constructions.exteriorContraction (n + 1) v a) +
      SymbolDifferential.Constructions.exteriorContraction n v (SymbolDifferential.Constructions.exteriorContraction (n + 1) u a) = 0 := by
  have h := exteriorContraction_squared n (u + v) a
  simp only [exteriorContraction_add_vector, map_add, exteriorContraction_squared, zero_add, add_zero] at h
  simpa only [add_comm] using h

theorem exteriorDoubleContraction_symbol_zero (ξ : E →L[ℝ] ℝ) (u v : E) (a : DifferentialForms.Manifold.Basic.FormValue E 1) :
    SymbolDifferential.Constructions.exteriorContraction 0 v (SymbolDifferential.Constructions.exteriorContraction 1 u (SymbolDifferential.Constructions.exteriorDifferentialSymbol 1 ξ a)) =
      ξ u • SymbolDifferential.Constructions.exteriorContraction 0 v a - ξ v • SymbolDifferential.Constructions.exteriorContraction 0 u a := by
  have h := congrArg (SymbolDifferential.Constructions.exteriorContraction 0 v) (SymbolDifferential.Constructions.exteriorSymbol_contraction 0 ξ u a)
  rw [map_add, map_smul, SymbolDifferential.Constructions.exteriorSymbol_contraction_zero] at h
  exact eq_sub_of_add_eq h

theorem exteriorDoubleContraction_symbol (n : ℕ) (ξ : E →L[ℝ] ℝ) (u v : E)
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    SymbolDifferential.Constructions.exteriorContraction (n + 1) v
        (SymbolDifferential.Constructions.exteriorContraction (n + 1 + 1) u (SymbolDifferential.Constructions.exteriorDifferentialSymbol (n + 1 + 1) ξ a)) -
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (SymbolDifferential.Constructions.exteriorContraction n v (SymbolDifferential.Constructions.exteriorContraction (n + 1) u a)) =
        ξ u • SymbolDifferential.Constructions.exteriorContraction (n + 1) v a - ξ v • SymbolDifferential.Constructions.exteriorContraction (n + 1) u a := by
  have h1 := congrArg (SymbolDifferential.Constructions.exteriorContraction (n + 1) v) (SymbolDifferential.Constructions.exteriorSymbol_contraction (n + 1) ξ u a)
  rw [map_add, map_smul] at h1
  have h2 := SymbolDifferential.Constructions.exteriorSymbol_contraction n ξ v (SymbolDifferential.Constructions.exteriorContraction (n + 1) u a)
  have h2' := eq_sub_of_add_eq h2
  rw [h2'] at h1
  have h1' := eq_sub_of_add_eq h1
  rw [h1']
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.ContractionAlgebra.Constructions
