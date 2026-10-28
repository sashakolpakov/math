import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Complex.Basic

/-! # Family Chart Data -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyChartData.Abelian

noncomputable section

/-! A compact interface for the exact relative identity-chart formulas. -/

open scoped _root_.Manifold ContDiff

def FamilyIdentityChartData
    {P V X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    (L H : P → Type)
    [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℂ (L p)] [∀ p, NormedSpace ℝ (L p)]
    [∀ p, TopologicalSpace (H p)] [∀ p, ChartedSpace (L p) (H p)] [∀ p, One (H p)]
    (c : ∀ p, OpenPartialHomeomorph (H p) V)
    (embed : ∀ p, H p → X) (e : OpenPartialHomeomorph X (P × V)) (B : Set P) : Prop :=
  ∀ p ∈ B,
    (1 : H p) ∈ (c p).source ∧ c p 1 = 0 ∧
    (c p).MDifferentiable (𝓘(ℝ, L p)) (𝓘(ℝ, V)) ∧
    (c p).source = (embed p) ⁻¹' e.source ∧
    (c p).target = {v | (p, v) ∈ e.target} ∧
    (∀ z ∈ (c p).source, c p z = (e (embed p z)).2) ∧
    (∀ v ∈ (c p).target, embed p ((c p).symm v) = e.symm (p, v)) ∧
    ContMDiffOn (𝓘(ℂ, L p)) (𝓘(ℂ, V)) ω (c p) (c p).source ∧
    ContMDiffOn (𝓘(ℂ, V)) (𝓘(ℂ, L p)) ω (c p).symm (c p).target

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyChartData.Abelian
