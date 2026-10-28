import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor

/-! # Base Changed Section Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.BaseChangedSectionConstants

noncomputable section

/-! A section of any base change of a pointed proper reduced connected scheme identifies all global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y S : Scheme.{u}}

theorem properField_iteratedBaseChangeSection_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : Y ⟶ X} {q : Y ⟶ S} {t : S ⟶ Spec (.of K)} (H : IsPullback a q p t)
    (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) (T : Over S) :
    IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app T).left.appTop := by
  have H' : IsPullback (Limits.pullback.snd T.hom q ≫ a) (Limits.pullback.fst T.hom q)
      p (T.hom ≫ t) := (IsPullback.of_hasPullback T.hom q).flip.paste_horiz H
  exact FieldBaseChangeConstants.properField_baseChangedSection_globalFunctions_isIso p x hx H'
    ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app T).left (Section.BaseChangeFunctor.familyBaseChangeSection_fst q y hy T)

theorem properField_iteratedBaseChangeSection_bijective
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : Y ⟶ X} {q : Y ⟶ S} {t : S ⟶ Spec (.of K)} (H : IsPullback a q p t)
    (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) (T : Over S) :
    Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app T).left.appTop := by
  have : IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app T).left.appTop :=
    properField_iteratedBaseChangeSection_isIso p x hx H y hy T
  exact ConcreteCategory.bijective_of_isIso _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.BaseChangedSectionConstants
