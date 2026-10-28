import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersections

/-! # Parameter Intersection Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersectionLifts

noncomputable section

/-! Compatible points of two closed loci lift to their intersection with exact projection identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M X Y T : Over S} (i : X ⟶ M) (j : Y ⟶ M)
variable (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ i = b ≫ j)

def closedParameterIntersectionLift : T ⟶ ParameterIntersections.closedParameterIntersection i j :=
  (ParameterIntersections.closedParameterIntersectionPointEquiv i j T).symm ⟨(a, b), h⟩

theorem closedParameterIntersectionLift_fst :
    closedParameterIntersectionLift i j a b h ≫ ParameterIntersections.closedParameterIntersectionFst i j = a :=
  congrArg (fun z => z.val.1) ((ParameterIntersections.closedParameterIntersectionPointEquiv i j T).apply_symm_apply ⟨(a, b), h⟩)

theorem closedParameterIntersectionLift_snd :
    closedParameterIntersectionLift i j a b h ≫ ParameterIntersections.closedParameterIntersectionSnd i j = b :=
  congrArg (fun z => z.val.2) ((ParameterIntersections.closedParameterIntersectionPointEquiv i j T).apply_symm_apply ⟨(a, b), h⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersectionLifts
