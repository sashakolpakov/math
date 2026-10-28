import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Empty Projective Parameter -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyProjectiveParameter.Core

noncomputable section

/-! The empty parameter scheme has an actual projective presentation
over every base, including the required closed embedding and base equality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def emptyParameterOver (S : Scheme.{u}) : Over S := Over.mk (Scheme.emptyTo S)

instance emptyParameterOver_isEmpty (S : Scheme.{u}) : IsEmpty (emptyParameterOver S).left :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

def emptyParameterProjectivePresentation (S : Scheme.{u}) :
    Has.Core.ProjectivePresentation (emptyParameterOver S) where
  dimension := 0
  embedding := Scheme.emptyTo (Has.Core.projectiveSpace S 0)
  closed := by
    change IsClosedImmersion (Scheme.emptyTo (Has.Core.projectiveSpace S 0) : (∅ : Scheme.{u}) ⟶ _)
    infer_instance
  over_base := Scheme.empty_ext _ _

theorem emptyParameter_isProjectiveOver (S : Scheme.{u}) :
    Has.Core.IsProjectiveOver (emptyParameterOver S) := ⟨emptyParameterProjectivePresentation S⟩

def emptyTestParameter {S : Scheme.{u}} (T : Over S) [IsEmpty T.left] :
    T ⟶ emptyParameterOver S :=
  Over.homMk (isInitialOfIsEmpty.to _) (isInitialOfIsEmpty.hom_ext _ _)

theorem emptyParameter_hom_subsingleton {S : Scheme.{u}} (T : Over S) :
    Subsingleton (T ⟶ emptyParameterOver S) := by
  refine ⟨fun a b => ?_⟩
  let : IsEmpty T.left := a.left.base.hom.1.isEmpty
  exact Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyProjectiveParameter.Core
