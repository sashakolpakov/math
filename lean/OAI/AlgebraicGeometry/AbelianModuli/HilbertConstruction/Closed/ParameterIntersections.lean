import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Parameter Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersections

noncomputable section

/-! Two closed parameter loci have an actual intersection with exact compatible pairs of points and a quasi-projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M X Y : Over S} (i : X ⟶ M) (j : Y ⟶ M)

def closedParameterIntersection : Over S := Over.mk (pullback.fst i.left j.left ≫ X.hom)

def closedParameterIntersectionFst : closedParameterIntersection i j ⟶ X :=
  Over.homMk (pullback.fst i.left j.left) rfl

def closedParameterIntersectionSnd : closedParameterIntersection i j ⟶ Y :=
  Over.homMk (pullback.snd i.left j.left) (by
    change pullback.snd i.left j.left ≫ Y.hom = pullback.fst i.left j.left ≫ X.hom
    rw [← i.w, ← j.w, ← pullback.condition_assoc])

theorem closedParameterIntersection_condition :
    closedParameterIntersectionFst i j ≫ i = closedParameterIntersectionSnd i j ≫ j :=
  Over.OverMorphism.ext (pullback.condition (f := i.left) (g := j.left))

instance closedParameterIntersectionFst_closed [IsClosedImmersion j.left] :
    IsClosedImmersion (closedParameterIntersectionFst i j).left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst i.left j.left))

def closedParameterIntersectionPointEquiv (T : Over S) :
    (T ⟶ closedParameterIntersection i j) ≃
      {p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ i = p.2 ≫ j} where
  toFun a := ⟨(a ≫ closedParameterIntersectionFst i j, a ≫ closedParameterIntersectionSnd i j), by
    simp only [Category.assoc, closedParameterIntersection_condition]⟩
  invFun p := Over.homMk (pullback.lift p.val.1.left p.val.2.left (congrArg Over.Hom.left p.property)) (by
    change pullback.lift p.val.1.left p.val.2.left _ ≫ (pullback.fst i.left j.left ≫ X.hom) = T.hom
    rw [pullback.lift_fst_assoc]
    exact p.val.1.w)
  left_inv a := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · exact Over.OverMorphism.ext (pullback.lift_snd _ _ _)

def closedParameterIntersectionQuasiProjectivePresentation [IsNoetherian S]
    [IsClosedImmersion j.left] (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (closedParameterIntersection i j) :=
  Q.ofClosedImmersion (closedParameterIntersectionFst i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersections
