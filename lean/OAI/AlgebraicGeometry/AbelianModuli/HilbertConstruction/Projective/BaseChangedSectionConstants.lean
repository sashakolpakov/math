import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

/-! # Base Changed Section Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangedSectionConstants

noncomputable section

/-! Every section of every base change of a pointed proper smooth geometrically connected projective family identifies global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem projectivePresentation_iteratedBaseChangeSection_isIso
    {S T Y : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    {a : Y ⟶ X.left} {q : Y ⟶ T} {t : T ⟶ S} (H : IsPullback a q X.hom t)
    (y : T ⟶ Y) (hy : y ≫ q = 𝟙 _) (U : Over T) :
    IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop := by
  have H' : IsPullback (Limits.pullback.snd U.hom q ≫ a) (Limits.pullback.fst U.hom q)
      X.hom (U.hom ≫ t) := (IsPullback.of_hasPullback U.hom q).flip.paste_horiz H
  have : IsIso (Limits.pullback.fst U.hom q).appTop :=
    UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso P x hx H'
  exact Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (Limits.pullback.fst U.hom q)
    ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left (Section.BaseChangeFunctor.familyBaseChangeSection_fst q y hy U)

theorem projectivePresentation_iteratedBaseChangeSection_bijective
    {S T Y : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    {a : Y ⟶ X.left} {q : Y ⟶ T} {t : T ⟶ S} (H : IsPullback a q X.hom t)
    (y : T ⟶ Y) (hy : y ≫ q = 𝟙 _) (U : Over T) :
    Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection q y hy).app U).left.appTop := by
  have := projectivePresentation_iteratedBaseChangeSection_isIso P x hx H y hy U
  exact ConcreteCategory.bijective_of_isIso _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangedSectionConstants
