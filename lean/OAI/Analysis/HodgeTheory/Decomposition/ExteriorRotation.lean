import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket
import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction

/-! # Exterior Rotation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ExteriorRotation.Constructions

noncomputable section

/-! The infinitesimal covector action and constant-direction exterior
derivatives have the exact commutator given by composition of directions. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem directionalExteriorDerivative_symbol (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative n A a x =
      ∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp A) (fderiv ℝ a x (b i)) :=
  CovectorSymbolAction.Constructions.alternation_comp_symbol_expansion b n (fderiv ℝ a x) A

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem covectorInfinitesimalAction_fderiv (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) :
    fderiv ℝ (fun y => CovectorConnection.Constructions.covectorInfinitesimalAction n A (a y)) x =
      (CovectorConnection.Constructions.covectorInfinitesimalAction n A).comp (fderiv ℝ a x) := by
  exact ((CovectorConnection.Constructions.covectorInfinitesimalAction n A).hasFDerivAt.comp x ha.hasFDerivAt).fderiv

theorem covectorInfinitesimalAction_directionalExterior (b : Module.Basis ι ℝ E) (n : ℕ)
    (A B : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) :
    CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) A (ExteriorConstantBracket.Constructions.directionalExteriorDerivative n B a x) -
      ExteriorConstantBracket.Constructions.directionalExteriorDerivative n B (fun y => CovectorConnection.Constructions.covectorInfinitesimalAction n A (a y)) x =
      ExteriorConstantBracket.Constructions.directionalExteriorDerivative n (B.comp A) a x := by
  rw [directionalExteriorDerivative_symbol b n, directionalExteriorDerivative_symbol b n,
    directionalExteriorDerivative_symbol b n, covectorInfinitesimalAction_fderiv n A a ha, map_sum]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [CovectorSymbolAction.Constructions.covectorInfinitesimalAction_exteriorSymbol]
  rw [Finset.sum_add_distrib, add_sub_cancel_right]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.ExteriorRotation.Constructions
