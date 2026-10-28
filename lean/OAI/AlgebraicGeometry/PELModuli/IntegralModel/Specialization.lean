import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
import Lean.Util.CollectAxioms

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-!
IntegralModel: properness and specialization of surjectivity on actual schemes.

This file proves the specialization mechanism on actual schemes. It does not
import any of the admitted statement files. The PEL construction and the
Albanese descent interfaces in the target specification are still separate
obligations; the theorem below is not advertised as the complete IntegralModel result.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Base changing a morphism gives the usual cartesian square on schemes. -/
theorem base_change_square {S T : Scheme.{u}} (g : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom g) ((Over.pullback g).map f).left
      f.left (pullback.fst Y.hom g) := by
  apply IsPullback.of_bot
      (v₂₁ := pullback.snd Y.hom g) (v₂₂ := Y.hom) (h₃₁ := g)
  · have hsnd : ((Over.pullback g).map f).left ≫ pullback.snd Y.hom g =
        pullback.snd X.hom g := pullback.lift_snd _ _ _
    rw [hsnd, f.w]
    exact IsPullback.of_hasPullback X.hom g
  · exact (pullback.lift_fst _ _ _).symm
  · exact IsPullback.of_hasPullback Y.hom g

/-- A proper map over a base is surjective if it becomes surjective over
a dominant base change and its target is open over the base. In particular,
this applies to the generic fiber when the target is an abelian scheme. -/
theorem surjective_of_dominant_base_change
    {S T : Scheme.{u}} (g : T ⟶ S) [IsDominant g]
    {X Y : Over S} (f : X ⟶ Y)
    [IsProper f.left] [UniversallyOpen Y.hom]
    (hgeneric : Surjective ((Over.pullback g).map f).left) :
    Surjective f.left := by
  let fT := ((Over.pullback g).map f).left
  have hT : Function.Surjective fT := hgeneric.surj
  have hdense : Dense (Y.hom ⁻¹' Set.range g) :=
    g.denseRange.preimage Y.hom.isOpenMap
  have hsub : Y.hom ⁻¹' Set.range g ⊆ Set.range f.left := by
    intro y hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨yT, hyT, _⟩ := Scheme.Pullback.exists_preimage_pullback y t ht.symm
    obtain ⟨xT, hxT⟩ := hT yT
    refine ⟨pullback.fst X.hom g xT, ?_⟩
    have heq : fT ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ f.left := by
      exact pullback.lift_fst _ _ _
    calc
      f.left (pullback.fst X.hom g xT) = pullback.fst Y.hom g (fT xT) :=
        (congrArg (fun h : (pullback X.hom g) ⟶ Y.left => h xT) heq).symm
      _ = y := by rw [hxT, hyT]
  let : IsDominant f.left := ⟨hdense.mono hsub⟩
  infer_instance

/-- Surjectivity obtained from the generic fiber persists after every
further base change, including arbitrary geometric special fibers. -/
theorem every_base_change_surjective
    {S T : Scheme.{u}} (g : T ⟶ S) [IsDominant g]
    {X Y : Over S} (f : X ⟶ Y)
    [IsProper f.left] [UniversallyOpen Y.hom]
    (hgeneric : Surjective ((Over.pullback g).map f).left)
    {U : Scheme.{u}} (t : U ⟶ S) :
    Surjective ((Over.pullback t).map f).left := by
  let : Surjective f.left := surjective_of_dominant_base_change g f hgeneric
  exact MorphismProperty.of_isPullback (P := @Surjective)
    (base_change_square t f) inferInstance

/-- Every geometric fiber is surjective on its algebraically closed field
points. This uses actual rational points, rather than just closed supports. -/
theorem every_geometric_fiber_point_surjective
    {S T : Scheme.{u}} (g : T ⟶ S) [IsDominant g]
    {X Y : Over S} (f : X ⟶ Y)
    [IsProper f.left] [UniversallyOpen Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hgeneric : Surjective ((Over.pullback g).map f).left)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S) :
    Function.Surjective
      (fun p : Over.mk (𝟙 (Spec (.of Ω))) ⟶ (Over.pullback t).obj X =>
        p ≫ (Over.pullback t).map f) := by
  let : Surjective ((Over.pullback t).map f).left :=
    every_base_change_surjective g f hgeneric t
  let : LocallyOfFiniteType ((Over.pullback t).obj X).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom t))
  let : LocallyOfFiniteType ((Over.pullback t).obj Y).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom t))
  intro q
  apply (Albanese.Construction.ClosedPoints.pointMap_range_iff
    ((Over.pullback t).obj X) ((Over.pullback t).obj Y)
    ((Over.pullback t).map f) q).mpr
  exact ((Over.pullback t).map f).left.surjective _

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
