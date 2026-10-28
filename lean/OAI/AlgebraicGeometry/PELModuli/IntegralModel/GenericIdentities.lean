import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Generic Identities -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericIdentities

/-!
Morphisms between the actual models are determined by their generic fibers.
This supplies the identity bridge for spread group laws, diagrams, and
sum-of-differences maps, without adding their compatibility as hypotheses.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Every field-valued base change of a smooth morphism is reduced. -/
theorem geometricallyReduced_of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd hcart
  let : Smooth snd := MorphismProperty.of_isPullback hcart inferInstance
  exact Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced snd

/-- A dominant base change has dense image in a family open over its base. -/
theorem base_change_projection_dominant
    {S T : Scheme.{u}} (g : T ⟶ S) [IsDominant g]
    (X : Over S) [UniversallyOpen X.hom] :
    IsDominant (pullback.fst X.hom g) := by
  constructor
  change Dense (Set.range (pullback.fst X.hom g))
  rw [Scheme.Pullback.range_fst]
  exact g.denseRange.preimage X.hom.isOpenMap

/-- Equality on a dominant fiber determines maps from reduced open families
to separated families. No scheme-theoretic compatibility is stored as data. -/
theorem hom_eq_of_dominant_base_change
    {S T : Scheme.{u}} (g : T ⟶ S) [IsDominant g]
    {X Y : Over S} [IsReduced X.left] [UniversallyOpen X.hom]
    [IsSeparated Y.hom] (f h : X ⟶ Y)
    (heq : (Over.pullback g).map f = (Over.pullback g).map h) : f = h := by
  let : IsDominant (pullback.fst X.hom g) := base_change_projection_dominant g X
  have hleft : pullback.fst X.hom g ≫ f.left = pullback.fst X.hom g ≫ h.left := by
    have he := congrArg
      (fun k => k.left ≫ pullback.fst Y.hom g) heq
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he
  ext1
  exact ext_of_isDominant_of_isSeparated Y.hom (f.w.trans h.w.symm)
    (pullback.fst X.hom g) hleft

/-- The hypotheses needed above hold for smooth models over a reduced
locally Noetherian arithmetic base. -/
theorem smooth_hom_eq_of_dominant_base_change
    {S T : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S]
    (g : T ⟶ S) [IsDominant g]
    {X Y : Over S} [Smooth X.hom] [IsSeparated Y.hom]
    (f h : X ⟶ Y)
    (heq : (Over.pullback g).map f = (Over.pullback g).map h) : f = h := by
  let : GeometricallyReduced X.hom := geometricallyReduced_of_smooth X.hom
  let : IsReduced X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.hom
  exact hom_eq_of_dominant_base_change g f h heq

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericIdentities
