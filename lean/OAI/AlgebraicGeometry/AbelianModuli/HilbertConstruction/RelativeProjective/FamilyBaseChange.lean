import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families

/-! # Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual arbitrary base change of closed families in relative projective space, with field-fiber Hilbert conditions preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {n : ℕ}

def Closed.Families.FlatClosedFamily.projectiveBaseChange (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n)) (f : T ⟶ S) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n) :=
  F.pullbackAlong (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n)

theorem Closed.Families.FlatClosedFamily.projectiveBaseChange_affine (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n))
    (f : T ⟶ S) {R : CommRingCat.{u}} (x : Spec R ⟶ T) :
    (F.projectiveBaseChange f).affineProjectivePullback x = F.affineProjectivePullback (x ≫ f) := by
  apply Closed.Families.FlatClosedFamily.ext
  exact (F.ideal.comap_comp (AffineProjective.Charts.affineProjectiveChartMap x n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)).symm.trans
    (congrArg (fun p => F.ideal.comap p) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_affine f n x))

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) (f : T ⟶ S) : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P where
  family := F.family.projectiveBaseChange f
  fieldHilbert K _ x := by
    rw [F.family.projectiveBaseChange_affine f x]
    exact F.fieldHilbert K (x ≫ f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
