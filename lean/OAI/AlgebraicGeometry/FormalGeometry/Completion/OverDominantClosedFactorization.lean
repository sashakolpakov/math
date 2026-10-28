import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantClosedFactorization
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Over Dominant Closed Factorization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OverDominantClosedFactorization.Construction

noncomputable section

/-! Closed factorization detected by dominance, with the structure
map to the base retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem overFactorThroughClosed_of_dominant {S : Scheme.{u}} {X Y Z W : Over S}
    (p : X ⟶ Y) [IsSchemeTheoreticallyDominant p.left]
    (f : Y ⟶ Z) (i : W ⟶ Z) [IsClosedImmersion i.left]
    (g : X ⟶ W) (hg : p ≫ f = g ≫ i) : ∃ h : Y ⟶ W, h ≫ i = f := by
  obtain ⟨h, hh⟩ := DominantClosedFactorization.Construction.factorThroughClosed_of_dominant p.left f.left i.left g.left (congrArg Over.Hom.left hg)
  refine ⟨Over.homMk h ?_, Over.OverMorphism.ext hh⟩
  rw [← i.w, ← Category.assoc, hh]
  exact f.w

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OverDominantClosedFactorization.Construction
