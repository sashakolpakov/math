import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Fiber Pullback Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition

noncomputable section

/-!
# Composition coherence for actual line-fiber pullback isomorphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {E : Over S} (L : Line.Bundles.LineBundle E.left)

/-- Iterating the actual fiber pullback isomorphisms agrees with the composite through the canonical pullback comparison. -/
theorem fiberIso_comp {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T') (hg : T'' ⟶ T)
    (hcomp : h ≫ g = hg) (x : T ⟶ E) (x' : T' ⟶ E) (x'' : T'' ⟶ E)
    (hx : g ≫ x = x') (hx' : h ≫ x' = x'') (hx'' : hg ≫ x = x'') :
    (Scheme.Modules.pullback h.left).mapIso (Line.Fibers.fiberPullbackIso L g x x' hx) ≪≫
        Line.Fibers.fiberPullbackIso L h x' x'' hx' =
      (Scheme.Modules.pullbackComp h.left g.left ≪≫
        Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hcomp)).app (Line.Fibers.fiber L x) ≪≫
        Line.Fibers.fiberPullbackIso L hg x x'' hx'' := by
  have he := GlobalFrameNaturality.comparison_pullback x L h g x' hx hg x'' hx'' hcomp hx'
  rw [GlobalPullbackFrame.comparison_eq, GlobalPullbackFrame.comparison_eq] at he
  exact he

/-- The composition formula with the composite test map itself needs only the ordinary pullback comparison. -/
theorem fiberIso_comp_exact {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T')
    (x : T ⟶ E) (x' : T' ⟶ E) (x'' : T'' ⟶ E)
    (hx : g ≫ x = x') (hx' : h ≫ x' = x'') (hx'' : (h ≫ g) ≫ x = x'') :
    (Scheme.Modules.pullback h.left).mapIso (Line.Fibers.fiberPullbackIso L g x x' hx) ≪≫
      Line.Fibers.fiberPullbackIso L h x' x'' hx' =
      (Scheme.Modules.pullbackComp h.left g.left).app (Line.Fibers.fiber L x) ≪≫
        Line.Fibers.fiberPullbackIso L (h ≫ g) x x'' hx'' := by
  have hc : (Scheme.Modules.pullbackComp h.left g.left ≪≫
      Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (rfl : h ≫ g = h ≫ g))).app (Line.Fibers.fiber L x) =
      (Scheme.Modules.pullbackComp h.left g.left).app (Line.Fibers.fiber L x) := by
    apply Iso.ext
    exact Category.comp_id _
  exact (fiberIso_comp L g h (h ≫ g) rfl x x' x'' hx hx' hx'').trans
    (congrArg (fun e => e ≪≫ Line.Fibers.fiberPullbackIso L (h ≫ g) x x'' hx'') hc)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition
