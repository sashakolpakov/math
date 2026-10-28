/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/Picard/DualPullback/RestrictComp.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionCompositionAdjunction

/-! # Restriction Pullback Composition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionPullbackComposition

/-! Compatibility of the restriction/pullback comparison with composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open Scheme.Modules

theorem restrictionComp_eq_adjoint {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctorComp f g =
    (Adjunction.leftAdjointCompIso (restrictAdjunction g) (restrictAdjunction f)
      (restrictAdjunction (f ≫ g)) (pushforwardComp f g)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((restrictAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  have h := unit_conjugateEquiv
    ((restrictAdjunction g).comp (restrictAdjunction f))
    (restrictAdjunction (f ≫ g))
    (Adjunction.leftAdjointCompIso (restrictAdjunction g) (restrictAdjunction f)
      (restrictAdjunction (f ≫ g)) (pushforwardComp f g)).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at h
  exact (RestrictionCompositionAdjunction.restrictionComp_unit f g M).trans h

theorem restrictionComp_mate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
    (pushforwardComp f g).hom := by
  rw [restrictionComp_eq_adjoint]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

theorem restrictionPullbackMiddle_mate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      ((restrictAdjunction g).comp (restrictAdjunction f))
      (Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
        Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom) =
      𝟙 (pushforward f ⋙ pushforward g) := by
  rw [← conjugateEquiv_comp
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f))]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

theorem restrictionPullback_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    (restrictFunctorComp f g).hom ≫
      Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
      Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom ≫
      (pullbackComp f g).hom = (restrictFunctorIsoPullback (f ≫ g)).hom := by
  let a := (restrictAdjunction (f ≫ g))
  let b := ((restrictAdjunction g).comp (restrictAdjunction f))
  let c := ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
  let d := (pullbackPushforwardAdjunction (f ≫ g))
  let t := Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
    Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom
  change (restrictFunctorComp f g).hom ≫ t ≫ (pullbackComp f g).hom = _
  apply (conjugateEquiv d a).injective
  rw [← Category.assoc, ← conjugateEquiv_comp d c a]
  rw [← conjugateEquiv_comp c b a]
  rw [PullbackCompositionMate.Scheme.Modules.conjugateEquiv_pullbackComp_hom,
    restrictionPullbackMiddle_mate, restrictionComp_mate]
  simp [a, d, restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

end OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionPullbackComposition
