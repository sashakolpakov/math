import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection
import OAI.Analysis.HodgeTheory.Decomposition.ContractionAlgebra

/-! # Covariant Insertion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovariantInsertion.Constructions

noncomputable section

section

/-! Covariant insertion calculus on genuine alternating covectors. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorInfinitesimalAction_contraction (n : ℕ) (A : E →L[ℝ] E)
    (w : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n w (CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) A a) =
      SymbolDifferential.Constructions.exteriorContraction n (A w) a + CovectorConnection.Constructions.covectorInfinitesimalAction n A (SymbolDifferential.Constructions.exteriorContraction n w a) := by
  ext v
  change CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) A a (Matrix.vecCons w v) =
    a (Matrix.vecCons (A w) v) + CovectorConnection.Constructions.covectorInfinitesimalAction n A (SymbolDifferential.Constructions.exteriorContraction n w a) v
  rw [CovectorConnection.Constructions.covectorInfinitesimalAction_apply, CovectorConnection.Constructions.covectorInfinitesimalAction_apply, Fin.sum_univ_succ]
  simp only [SymbolDifferential.Constructions.exteriorContraction_apply]
  congr 1
  · apply congrArg a
    funext j
    cases j using Fin.cases <;> simp
  · apply Finset.sum_congr rfl
    intro i _
    change a (Function.update (Matrix.vecCons w v) i.succ (A (v i))) =
      a (Matrix.vecCons w (Function.update v i (A (v i))))
    congr 1
    funext j
    cases j using Fin.cases with
    | zero =>
      rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
      rfl
    | succ j =>
      by_cases hj : j = i
      · subst j; simp
      · simp [hj, Function.update_of_ne]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem exteriorContraction_fderiv (n : ℕ) (a : D → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (w : D → E)
    {x : D} (ha : DifferentiableAt ℝ a x) (hw : DifferentiableAt ℝ w x) (u : D) :
    fderiv ℝ (fun y => SymbolDifferential.Constructions.exteriorContraction n (w y) (a y)) x u =
      SymbolDifferential.Constructions.exteriorContraction n (fderiv ℝ w x u) (a x) +
        SymbolDifferential.Constructions.exteriorContraction n (w x) (fderiv ℝ a x u) := by
  let L : DifferentialForms.Manifold.Basic.FormValue E (n + 1) →L[ℝ] E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
    ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap
  have hL : HasFDerivAt L L (a x) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := DifferentialForms.Manifold.Basic.FormValue E (n + 1))
      (F := E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) L
  have hc := HasFDerivAt.comp (E := D) (F := DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (G := E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) x hL ha.hasFDerivAt
  have h := congrArg (fun K : D →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n => K u) (hc.clm_apply hw.hasFDerivAt).fderiv
  exact h

end

/-! The induced form connection commutes with insertion when both the
vector and the covector are differentiated by their actual connections. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exteriorContraction_smoothOn (n : ℕ) (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (w : E → E)
    {U : Set E} (ha : ContDiffOn ℝ ∞ a U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun y => SymbolDifferential.Constructions.exteriorContraction n (w y) (a y)) U := by
  let L : DifferentialForms.Manifold.Basic.FormValue E (n + 1) →L[ℝ] E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
    ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap
  have hL : ContDiff ℝ ∞ L := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (F := E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) L
  exact (hL.comp_contDiffOn ha).clm_apply hw

theorem covectorConnectionDerivative_contraction (n : ℕ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (w : E → E)
    {x : E} (ha : DifferentiableAt ℝ a x) (hw : DifferentiableAt ℝ w x) (u : E) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => SymbolDifferential.Constructions.exteriorContraction n (w y) (a y)) x u =
      SymbolDifferential.Constructions.exteriorContraction n (fderiv ℝ w x u + Γ x u (w x)) (a x) +
        SymbolDifferential.Constructions.exteriorContraction n (w x) (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1) Γ a x u) := by
  rw [CovectorConnection.Constructions.covectorConnectionDerivative_apply, exteriorContraction_fderiv n a w ha hw,
    CovectorConnection.Constructions.covectorConnectionDerivative_apply, map_sub, ContractionAlgebra.Constructions.exteriorContraction_add_vector,
    covectorInfinitesimalAction_contraction]
  abel

theorem covectorConnectionDerivative_const_contraction (n : ℕ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (w : E)
    {x : E} (ha : DifferentiableAt ℝ a x) (u : E) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => SymbolDifferential.Constructions.exteriorContraction n w (a y)) x u =
      SymbolDifferential.Constructions.exteriorContraction n (Γ x u w) (a x) +
        SymbolDifferential.Constructions.exteriorContraction n w (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1) Γ a x u) := by
  have h := covectorConnectionDerivative_contraction n Γ a (fun _ => w) ha (differentiableAt_const w) u
  rw [(hasFDerivAt_const w x).fderiv, zero_apply, zero_add] at h
  exact h

end

end OAI.Analysis.HodgeTheory.Decomposition.CovariantInsertion.Constructions
