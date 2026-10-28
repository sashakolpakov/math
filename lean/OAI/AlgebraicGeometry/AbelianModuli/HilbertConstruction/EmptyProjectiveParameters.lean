import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.Representation

/-! # Empty Projective Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveParameters

noncomputable section

/-! An actual empty projective parameter scheme over any base, with its locally noetherian test-category object when the base is locally noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def emptyProjectiveParameter (S : Scheme.{u}) : Over S :=
  Over.mk ((⊤ : (Projective.ProjectivePresentations.projectiveSpaceOver S 0).left.IdealSheafData).subschemeι ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S 0).hom)

instance emptyProjectiveParameter_isEmpty (S : Scheme.{u}) : IsEmpty (emptyProjectiveParameter S).left :=
  inferInstanceAs (IsEmpty (⊤ : (Projective.ProjectivePresentations.projectiveSpaceOver S 0).left.IdealSheafData).subscheme)

def emptyParameterProjectivePresentation (S : Scheme.{u}) : Projective.ProjectivePresentations.ProjectivePresentation (emptyProjectiveParameter S) where
  dimension := 0
  embedding := Over.homMk (⊤ : (Projective.ProjectivePresentations.projectiveSpaceOver S 0).left.IdealSheafData).subschemeι rfl
  closedImmersion := inferInstanceAs (IsClosedImmersion (⊤ : (Projective.ProjectivePresentations.projectiveSpaceOver S 0).left.IdealSheafData).subschemeι)

def emptyLocallyNoetherianParameter (S : Scheme.{u}) [IsLocallyNoetherian S] : Relative.Functor.LocallyNoetherianTest S where
  obj := emptyProjectiveParameter S
  property := by
    have : IsProper (emptyProjectiveParameter S).hom := (emptyParameterProjectivePresentation S).proper
    exact LocallyOfFiniteType.isLocallyNoetherian (emptyProjectiveParameter S).hom

instance emptyLocallyNoetherianParameter_isEmpty (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsEmpty (emptyLocallyNoetherianParameter S).obj.left := emptyProjectiveParameter_isEmpty S

def overEmptySourceMap {S : Scheme.{u}} (T Z : Over S) [IsEmpty T.left] : T ⟶ Z :=
  Over.homMk (isInitialOfIsEmpty.to Z.left) (isInitialOfIsEmpty.hom_ext _ _)

theorem overEmptySourceMap_unique {S : Scheme.{u}} {T Z : Over S} [IsEmpty T.left] (f g : T ⟶ Z) : f = g :=
  Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext f.left g.left)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveParameters
