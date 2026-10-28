import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals

/-! # Condition Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! A closed condition model gives a natural representing isomorphism of functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M : Over S} {P : Subfunctor (yoneda.obj M)} (D : ConditionIdeals.ClosedConditionModel P)

def ConditionIdeals.ClosedConditionModel.pointMap : yoneda.obj D.scheme ⟶ P.toFunctor where
  app T := TypeCat.ofHom (fun g => ⟨g ≫ D.inclusion, (D.factorization T.unop _).mpr
    ⟨g, rfl, fun h hh => by
      have : Mono D.inclusion := Over.mono_of_mono_left D.inclusion
      exact (cancel_mono D.inclusion).mp hh⟩⟩)
  naturality := by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    exact Category.assoc _ _ _

instance ConditionIdeals.ClosedConditionModel.pointMap_isIso : IsIso D.pointMap := by
  have : Mono D.inclusion := Over.mono_of_mono_left D.inclusion
  apply (NatTrans.isIso_iff_isIso_app D.pointMap).mpr
  intro T
  apply (isIso_iff_bijective (D.pointMap.app T)).mpr
  constructor
  · intro g h he
    apply (cancel_mono D.inclusion).mp
    exact congrArg Subtype.val he
  · intro x
    obtain ⟨g, hg, _⟩ := (D.factorization T.unop x.val).mp x.property
    exact ⟨g, Subtype.ext hg⟩

def ConditionIdeals.ClosedConditionModel.representation : yoneda.obj D.scheme ≅ P.toFunctor := asIso D.pointMap

theorem ConditionIdeals.ClosedConditionModel.representation_inclusion : D.representation.hom ≫ P.ι = yoneda.map D.inclusion := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
