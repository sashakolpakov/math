import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Equalizer -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Equalizer

noncomputable section

/-! The scheme equalizer of maps over the complex base detects
equality of their values at every closed point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))} (f g : X ⟶ Y) [IsSeparated Y.hom]

def locus : Closeds X.left :=
  ⟨Set.range (equalizer.ι f g).left, (equalizer.ι f g).left.isClosedEmbedding.isClosed_range⟩

theorem eq_of_mem (x : X.left) (hx : x ∈ locus f g) : f.left x = g.left x := by
  obtain ⟨z, rfl⟩ := hx
  exact congrArg (fun a : equalizer f g ⟶ Y => a.left z) (equalizer.condition f g)

theorem mem_of_closed [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (x : X.left) (hx : IsClosed ({x} : Set _)) (he : f.left x = g.left x) : x ∈ locus f g := by
  let p := pointOfClosedPoint X.hom x hx
  have hp : p ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let p' : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X := Over.homMk p hp
  have heq : p' ≫ f = p' ≫ g := by
    apply Over.OverMorphism.ext
    apply ext_of_apply_closedPoint_eq Y.hom
      (show (p ≫ f.left) ≫ Y.hom = 𝟙 _ by rw [Category.assoc, f.w]; exact hp)
      (show (p ≫ g.left) ≫ Y.hom = 𝟙 _ by rw [Category.assoc, g.w]; exact hp)
    simpa only [Scheme.Hom.comp_apply, p, pointOfClosedPoint_apply] using he
  refine ⟨(equalizer.lift p' heq).left (IsLocalRing.closedPoint ℂ), ?_⟩
  have h := congrArg (fun a : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X =>
    a.left (IsLocalRing.closedPoint ℂ)) (equalizer.lift_ι p' heq)
  exact h.trans (pointOfClosedPoint_apply _ _ _ _)

theorem mem_iff_closed [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (x : X.left) (hx : IsClosed ({x} : Set _)) :
    x ∈ locus f g ↔ f.left x = g.left x :=
  ⟨eq_of_mem f g x, mem_of_closed f g x hx⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Equalizer
