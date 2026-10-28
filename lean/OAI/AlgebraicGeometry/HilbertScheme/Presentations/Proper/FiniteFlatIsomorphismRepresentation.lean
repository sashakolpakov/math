import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismLocus
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Finite Flat Isomorphism Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismRepresentation

noncomputable section

/-! An actual open scheme represents the finite-flat relative
isomorphism functor on all scheme tests, with its inclusion compatibility. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B)
variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [IsProper q]

def properFiniteFlatIsomorphismSubfunctor : Subfunctor (yoneda.obj B) where
  obj T := {g | IsIso (pullback.snd f (pullback.fst q g))}
  map a g hg := by
    apply (FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_range f q (a.unop ≫ g)).mpr
    rintro b ⟨t, rfl⟩
    exact (FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_range f q g).mp hg ⟨a.unop t, rfl⟩

def properFiniteFlatIsomorphismPointMap :
    yoneda.obj (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).toScheme ⟶
      (properFiniteFlatIsomorphismSubfunctor f q).toFunctor where
  app T := ↾fun (g : T.unop ⟶ (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).toScheme) =>
    ⟨g ≫ (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).ι,
    (FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_range f q _).mpr (by
      rintro b ⟨t, rfl⟩
      exact (g t).property)⟩
  naturality T U a := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    exact Category.assoc _ _ _

theorem properFiniteFlatIsomorphismPointMap_isIso :
    IsIso (properFiniteFlatIsomorphismPointMap f q) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro g h he
    apply (cancel_mono (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).ι).mp
    exact congrArg Subtype.val he
  · intro g
    obtain ⟨h, hh, _⟩ := (FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_unique_lift f q g.val).mp g.property
    exact ⟨h, Subtype.ext hh⟩

def properFiniteFlatIsomorphismRepresentation :
    yoneda.obj (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).toScheme ≅
      (properFiniteFlatIsomorphismSubfunctor f q).toFunctor := by
  let := properFiniteFlatIsomorphismPointMap_isIso f q
  exact asIso (properFiniteFlatIsomorphismPointMap f q)

theorem properFiniteFlatIsomorphismRepresentation_inclusion :
    (properFiniteFlatIsomorphismRepresentation f q).hom ≫
      (properFiniteFlatIsomorphismSubfunctor f q).ι =
        yoneda.map (FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).ι := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismRepresentation
