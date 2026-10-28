import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SupportBound
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualCoordinateStep

/-! # Cone Residual Step -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ConeResidualStep

noncomputable section

/-! One actual cone-intersection cycle equals the original generator
plus a residual cycle whose intersections improve by one codimension.
All coefficients are the native ambient Tor multiplicities. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap] (W : X.DimensionCycleSupport p) (hp : 1 ≤ p)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) (k : τ → ℕ)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ ResidualIntersection.Step.intersection X W.val (Z t) → k t ≤ X.supportCodimension C) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ y : X.carrier, ∃ a, (L a).val ∉ (X.embedding y).asHomogeneousIdeal)
      (hL : LinearIndependent ℂ L),
      Cone.SupportBound.IntegralCycle.cycle X m L hL h p W W = 1 ∧
      Cone.SupportBound.IntegralCycle.cycle X m L hL h p W =
        Finsupp.single W 1 + Cone.SupportBound.IntegralCycle.residual X m L hL h p W ∧
      ∀ t, ∀ D ∈ (Cone.SupportBound.IntegralCycle.residual X m L hL h p W).support,
        ∀ C : IrreducibleCloseds X.carrier,
          (C : Set X.carrier) ⊆ (D.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
          min (p + X.supportCodimension (Z t)) (k t + 1) ≤ X.supportCodimension C := by
  have hW : 1 ≤ X.supportCodimension W.val := W.property.symm ▸ hp
  obtain ⟨L, h, hL, ⟨x, hxW, _, ⟨U, hxU, hU⟩, _⟩, hres⟩ :=
    ResidualCoordinateStep.exists_coordinates X m W.val hW Z k hbound
  let := hU
  refine ⟨L, h, hL, Cone.SupportBound.IntegralCycle.original_coefficient X m L hL h p W U x hxW hxU,
    Cone.SupportBound.IntegralCycle.decomposition X m L hL h p W, ?_⟩
  intro t D hD C hC
  have hs := Cone.SupportBound.IntegralCycle.residual_supported X m L hL h p W U x hxW hxU D hD
  have hb := hres t C (fun y hy => ⟨hs (hC hy).1, (hC hy).2⟩)
  rw [W.property] at hb
  exact hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ConeResidualStep
