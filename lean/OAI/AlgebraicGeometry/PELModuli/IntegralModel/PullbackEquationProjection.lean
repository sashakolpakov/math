import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Pullback Equation Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackEquationProjection

noncomputable section

/-! Equality after actual scheme base change is equality of the two
original maps precomposed with the actual pullback projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem pullback_equation_iff_projection {S T : Scheme.{0}} {X Y : Over S}
    (l r : X ⟶ Y) (t : T ⟶ S) :
    (Over.pullback t).map l = (Over.pullback t).map r ↔
      pullback.fst X.hom t ≫ l.left = pullback.fst X.hom t ≫ r.left := by
  constructor
  · intro h
    have he := congrArg (fun q => q.left ≫ pullback.fst Y.hom t) h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, pullback.lift_fst] using h
    · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem projection_range_subset_equalizer_of_equation {S T : Scheme.{0}} {X Y : Over S}
    (l r : X ⟶ Y) (t : T ⟶ S)
    (h : (Over.pullback t).map l = (Over.pullback t).map r) :
    Set.range (pullback.fst X.hom t) ⊆ Set.range (equalizer.ι l r).left := by
  let Z : Over S := Over.mk (pullback.fst X.hom t ≫ X.hom)
  let p : Z ⟶ X := Over.homMk (pullback.fst X.hom t) rfl
  have he : p ≫ l = p ≫ r := Over.OverMorphism.ext ((pullback_equation_iff_projection l r t).mp h)
  let q := equalizer.lift p he
  rintro _ ⟨z, rfl⟩
  exact ⟨q.left z, congrArg (fun f => f.left z) (equalizer.lift_ι p he)⟩

theorem pullback_equation_precomp {S T U : Scheme.{0}} {X Y : Over S}
    (l r : X ⟶ Y) (t : T ⟶ S) (u : U ⟶ T)
    (h : (Over.pullback t).map l = (Over.pullback t).map r) :
    (Over.pullback (u ≫ t)).map l = (Over.pullback (u ≫ t)).map r := by
  let p : pullback X.hom (u ≫ t) ⟶ pullback X.hom t :=
    pullback.lift (pullback.fst X.hom (u ≫ t)) (pullback.snd X.hom (u ≫ t) ≫ u)
      (by rw [Category.assoc]; exact pullback.condition)
  have hp : p ≫ pullback.fst X.hom t = pullback.fst X.hom (u ≫ t) := pullback.lift_fst _ _ _
  apply (pullback_equation_iff_projection l r (u ≫ t)).mpr
  have he := congrArg (p ≫ ·) ((pullback_equation_iff_projection l r t).mp h)
  simpa only [← Category.assoc, hp] using he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackEquationProjection
