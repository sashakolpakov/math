import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ConeResidualStep
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SupportBound

/-! # Compatible Residual Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleResidualCoordinates

noncomputable section

/-! Residual coordinates can preserve every already proper fixed
intersection while improving the other prescribed bounds. The full
cone support, not just its nonzero coefficients, remains proper. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : 1 ≤ p) (W : X.DimensionCycleSupport p)
    {τ ι : Type} [Finite τ] [Finite ι] (Z : τ → IrreducibleCloseds X.carrier)
    (B : ι → X.DimensionCycleSupport q) (k : τ → ℕ)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ (Z t : Set X.carrier) → k t ≤ X.supportCodimension C)
    (hproper : ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ y : X.carrier, ∃ a, (L a).val ∉ (X.embedding y).asHomogeneousIdeal)
      (hL : LinearIndependent ℂ L),
      Cone.SupportBound.IntegralCycle.cycle X m L hL h p W =
        Finsupp.single W 1 + Cone.SupportBound.IntegralCycle.residual X m L hL h p W ∧
      (∀ i, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ (Cone.SupportBound.IntegralCycle.intersection X m L hL h p W : Set X.carrier) ∩
          ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) ∧
      (∀ t, ∀ D ∈ (Cone.SupportBound.IntegralCycle.residual X m L hL h p W).support,
        ∀ C : IrreducibleCloseds X.carrier,
          (C : Set X.carrier) ⊆ (D.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
            min (p + X.supportCodimension (Z t)) (k t + 1) ≤ X.supportCodimension C) ∧
      (∀ i, ∀ D ∈ (Cone.SupportBound.IntegralCycle.residual X m L hL h p W).support,
        ∀ C : IrreducibleCloseds X.carrier,
          (C : Set X.carrier) ⊆ (D.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) →
            p + q ≤ X.supportCodimension C) := by
  let S := Sum.elim Z (fun i => (B i).val)
  let kS := Sum.elim k (fun _ : ι => p + q)
  have hS : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ ResidualIntersection.Step.intersection X W.val (S t) → kS t ≤ X.supportCodimension C := by
    intro t C hC
    cases t with
    | inl t => exact hbound t C hC
    | inr i => exact hproper i C hC
  have hW : 1 ≤ X.supportCodimension W.val := W.property.symm ▸ hp
  obtain ⟨L, h, hL, ⟨x, hxW, _, ⟨U, hxU, hU⟩, _⟩, hres⟩ :=
    ResidualCoordinateStep.exists_coordinates X m W.val hW S kS hS
  let := hU
  have hfixed (i : ι) (C : IrreducibleCloseds X.carrier)
      (hC : (C : Set X.carrier) ⊆
        (ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) W.val : Set X.carrier) ∩
          ((B i).val : Set X.carrier)) : p + q ≤ X.supportCodimension C := by
    have hr := hres (Sum.inr i) C hC
    change min (X.supportCodimension W.val + X.supportCodimension (B i).val) ((p + q) + 1) ≤ X.supportCodimension C at hr
    rw [W.property, (B i).property, min_eq_left (Nat.le_succ (p + q))] at hr
    exact hr
  refine ⟨L, h, hL, Cone.SupportBound.IntegralCycle.decomposition X m L hL h p W, ?_, ?_, ?_⟩
  · intro i C hC
    exact Cone.SupportBound.cone X m L hL h p q W (B i) (hproper i) (hfixed i) C hC
  · intro t D hD C hC
    have hs := Cone.SupportBound.IntegralCycle.residual_supported X m L hL h p W U x hxW hxU D hD
    have hr := hres (Sum.inl t) C (fun y hy => ⟨hs (hC hy).1, (hC hy).2⟩)
    change min (X.supportCodimension W.val + X.supportCodimension (Z t)) (k t + 1) ≤ X.supportCodimension C at hr
    rw [W.property] at hr
    exact hr
  · intro i D hD C hC
    have hs := Cone.SupportBound.IntegralCycle.residual_supported X m L hL h p W U x hxW hxU D hD
    exact hfixed i C (fun y hy => ⟨hs (hC hy).1, (hC hy).2⟩)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleResidualCoordinates
