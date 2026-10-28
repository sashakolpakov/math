import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition

/-! # Chow Pushforward Composition -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardComposition

noncomputable section

/-! Composition of the exact linear Chow pushforwards. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

theorem comp {X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) (m n k p q r : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] [SmoothOfRelativeDimension k Z.structureMap]
    (hf : p + n = q + m) (hg : q + k = r + n) (hfg : p + k = r + m)
    (a : ProperCycleLinearity.ChowQ X p) :
    ChowPushforwardMap.map g n k q r hg (ChowPushforwardMap.map f m n p q hf a) = ChowPushforwardMap.map (f ≫ g) m k p r hfg a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  rw [ChowPushforwardMap.map_mk, ChowPushforwardMap.map_mk, PushforwardComposition.cycle_comp f g n k p q r hg, ChowPushforwardMap.map_mk]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardComposition
