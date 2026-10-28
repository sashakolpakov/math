import OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleSectionIso
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Etale Degree One -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleDegreeOne.Construction

noncomputable section

/-!
# Completion: an isomorphic nonempty base change detects degree one

The degree of a finite flat finitely presented morphism is locally
constant. On a connected base, degree one on any nonempty base change
therefore proves that the original morphism is an isomorphism.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- One isomorphic nonempty base change forces a finite flat cover of a connected base
to have degree one everywhere. -/
theorem finite_flat_isIso_of_baseChange_isIso {X Y Z : Scheme.{u}}
    [PreconnectedSpace Y] [Nonempty Z] (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (g : Z ⟶ Y)
    [IsIso (pullback.snd f g)] : IsIso f := by
  let z : Z := Nonempty.some inferInstance
  apply f.isIso_iff_finrank_eq.mpr
  ext y
  calc
    f.finrank y = f.finrank (g z) :=
      f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y (g z)
    _ = (pullback.snd f g).finrank z := (f.finrank_pullback_snd g z).symm
    _ = 1 := congrFun (Scheme.Hom.finrank_eq_one_of_isIso (pullback.snd f g)) z

/-- A connected sectioned base change proves that the original finite étale cover is trivial. -/
theorem finite_etale_isIso_of_connected_sectioned_baseChange {X Y Z : Scheme.{u}}
    [PreconnectedSpace Y] [Nonempty Z] (f : X ⟶ Y) [IsFinite f] [Etale f] (g : Z ⟶ Y)
    [PreconnectedSpace (pullback f g : Scheme.{u})] (s : Z ⟶ pullback f g)
    (hs : s ≫ pullback.snd f g = 𝟙 Z) : IsIso f := by
  have := EtaleSectionIso.Construction.connected_etale_section_isIso (pullback.snd f g) s hs
  exact finite_flat_isIso_of_baseChange_isIso f g

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleDegreeOne.Construction
