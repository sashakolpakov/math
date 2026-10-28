import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.SourceChow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ComponentRestriction

/-! # Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Chow

noncomputable section

/-! The full native Chow projection formula for arbitrary smooth
projective presentations, including disconnected source and target. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

theorem chow {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver)
    (m n p q s : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hd : q + n = s + m) (a : ProperCycleLinearity.ChowQ Y p) (b : ProperCycleLinearity.ChowQ X q) :
    ChowPushforwardMap.map f m n (p + q) (p + s) (by omega)
      (GeneralChowIntersection.chowMap X m p q (ChowPullback.pull P f m n p a) b) =
      GeneralChowIntersection.chowMap Y n p s a (ChowPushforwardMap.map f m n q s hd b) := by
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  let : ∀ C : irreducibleComponents X.carrier,
      SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m
  have hb : ProperCycleLinearity.cycleToChowQ X q b = ∑ C : irreducibleComponents X.carrier,
      ChowPushforwardMap.map (Component.Image.inclusion X C) m m q q rfl
        (ProperCycleLinearity.cycleToChowQ (X.componentVariety C).presentation q (Component.CycleMaps.restrict X C q b)) := by
    simp only [ChowPushforwardMap.map_mk, ← Component.CycleMaps.embed_eq_pushforward, ← map_sum,
      Component.Principal.CycleDecomposition.sum_embed_restrict]
  rw [hb]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [ClopenChow.intersection (Component.Image.inclusion X C) m p q,
    ComponentRestriction.pull m P f n C p,
    ChowPushforwardComposition.comp, ChowPushforwardComposition.comp]
  exact Integral.SourceChow.Projection.chow (ProductRestriction.presentation P (Component.Image.inclusion X C))
    (Component.Image.inclusion X C ≫ f) m n p q s hd a
    (ProperCycleLinearity.cycleToChowQ (X.componentVariety C).presentation q (Component.CycleMaps.restrict X C q b))

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Chow
