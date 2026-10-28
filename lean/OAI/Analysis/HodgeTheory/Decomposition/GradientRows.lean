import OAI.Analysis.HodgeTheory.Decomposition.VectorGradient
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Gradient Rows -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GradientRows.Constructions

noncomputable section

/-! First-order systems acting on genuine normalized vector gradients,
and their weighted quadratic coefficient operator. -/

open _root_.MeasureTheory
open scoped ContDiff BigOperators

variable {F G H ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [CompleteSpace F] [Fintype ι]

variable [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

def normalizedGradientComponent (i : ι) : PiLp 2 (fun _ : ι => F) →L[ℝ] F :=
  (((2 * Real.pi * Complex.I : ℂ) • ContinuousLinearMap.id ℂ F).comp
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => F)).toContinuousLinearMap)).restrictScalars ℝ

omit [CompleteSpace F] [Fintype ι] in
theorem normalizedGradientComponent_apply (i : ι) (v : PiLp 2 (fun _ : ι => F)) :
    normalizedGradientComponent i v = (2 * Real.pi * Complex.I : ℂ) • v i := rfl

def normalizedGradientRow (S : ι → F →L[ℝ] G) : PiLp 2 (fun _ : ι => F) →L[ℝ] G :=
  ∑ i, (S i).comp (normalizedGradientComponent i)

omit [CompleteSpace F] [CompleteSpace G] in
theorem normalizedGradientRow_apply (S : ι → F →L[ℝ] G) (v : PiLp 2 (fun _ : ι => F)) :
    normalizedGradientRow S v = ∑ i, S i ((2 * Real.pi * Complex.I : ℂ) • v i) := by
  simp only [normalizedGradientRow, sum_apply, ContinuousLinearMap.comp_apply,
    normalizedGradientComponent_apply]

def weightedGradientGram (S : ι → F →L[ℝ] G) (A : G →L[ℝ] G) :
    PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F) :=
  (normalizedGradientRow S).adjoint.comp (A.comp (normalizedGradientRow S))

theorem weightedGradientGram_pair (S : ι → F →L[ℝ] G) (A : G →L[ℝ] G)
    (v w : PiLp 2 (fun _ : ι => F)) :
    inner ℝ (weightedGradientGram S A v) w =
      inner ℝ (A (normalizedGradientRow S v)) (normalizedGradientRow S w) := by
  change inner ℝ ((normalizedGradientRow S).adjoint (A (normalizedGradientRow S v))) w = _
  exact ContinuousLinearMap.adjoint_inner_left (normalizedGradientRow S) w (A (normalizedGradientRow S v))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Set E} {S : E → ι → F →L[ℝ] G} {A : E → G →L[ℝ] G}

omit [CompleteSpace F] [CompleteSpace G] in
theorem normalizedGradientRow_smooth (hS : ∀ i, ContDiffOn ℝ ∞ (fun x => S x i) U) :
    ContDiffOn ℝ ∞ (fun x => normalizedGradientRow (S x)) U :=
  ContDiffOn.sum (fun i _ => (hS i).clm_comp contDiffOn_const)

theorem weightedGradientGram_smooth (hS : ∀ i, ContDiffOn ℝ ∞ (fun x => S x i) U)
    (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => weightedGradientGram (S x) (A x)) U := by
  have hrow := normalizedGradientRow_smooth hS
  have hAdj : ContDiff ℝ ∞
      (ContinuousLinearMap.adjoint : (PiLp 2 (fun _ : ι => F) →L[ℝ] G) → G →L[ℝ] PiLp 2 (fun _ : ι => F)) :=
    (ContinuousLinearMap.adjoint : (PiLp 2 (fun _ : ι => F) →L[ℝ] G) ≃ₗᵢ[ℝ]
      (G →L[ℝ] PiLp 2 (fun _ : ι => F))).toContinuousLinearEquiv.contDiff
  have hadj : ContDiffOn ℝ ∞ (fun x => (normalizedGradientRow (S x)).adjoint) U :=
    hAdj.comp_contDiffOn hrow
  exact hadj.clm_comp (hA.clm_comp hrow)

end

end OAI.Analysis.HodgeTheory.Decomposition.GradientRows.Constructions
