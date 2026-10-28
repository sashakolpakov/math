import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenScalar

/-! # Nested Single Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NestedSinglePushforward

noncomputable section

/-! The original two module pushforwards retain their literal source
presheaf when passing to the actual single-complex coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) (N : Y.Modules)

abbrev restriction := Reference.SinglePushforward.presheaves (f ≫ i)

def coefficientIso : Reference.SinglePresheafCoordinates.presheaf (PrincipalSource.OpenRestriction.image f i N) ≅
    (restriction f i).obj (Reference.SinglePresheafCoordinates.presheaf N) := Iso.refl _

def plainIso (c : ℕ) :
    Relative.AdditiveCechConcentration.coefficients ((single Z.Modules (.up ℕ) c).obj (PrincipalSource.OpenRestriction.image f i N)) ≅
    ((restriction f i).mapHomologicalComplex (.up ℕ)).obj
      ((single (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj
        (Reference.SinglePresheafCoordinates.presheaf N)) :=
  Reference.SinglePresheafCoordinates.iso (PrincipalSource.OpenRestriction.image f i N) c ≪≫
    (single (Z.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).mapIso (coefficientIso f i N) ≪≫
      ((singleMapHomologicalComplex (restriction f i) (.up ℕ) c).app
        (Reference.SinglePresheafCoordinates.presheaf N)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NestedSinglePushforward
