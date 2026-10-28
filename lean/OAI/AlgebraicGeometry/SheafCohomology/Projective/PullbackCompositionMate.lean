/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/Picard/DualPullback/RestrictComp.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pullback Composition Mate -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackCompositionMate.Scheme.Modules

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! The forward pullback-composition mate, from Mathlib's inverse mate. -/

open _root_.CategoryTheory
universe u

theorem conjugateEquiv_pullbackComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  have h : conjugateIsoEquiv
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).symm =
      pushforwardComp f g := Iso.ext (conjugateEquiv_pullbackComp_inv f g)
  exact congrArg Iso.inv h

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackCompositionMate.Scheme.Modules
