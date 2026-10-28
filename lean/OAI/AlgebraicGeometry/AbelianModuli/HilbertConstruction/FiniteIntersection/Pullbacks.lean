import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions

/-! # Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Pullbacks

noncomputable section

/-! The original finite intersection diagram has the expected pullback squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isPullback_homOfLE_of_eq_inf {Y : Scheme.{u}} {A B C D : Y.Opens}
    (hAB : A ≤ B) (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D)
    (hA : A = B ⊓ C) :
    IsPullback (Y.homOfLE hAB) (Y.homOfLE hAC) (Y.homOfLE hBD) (Y.homOfLE hCD) := by
  subst A
  exact isPullback_opens_inf_le hBD hCD

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

theorem finiteIntersection_isPullback {S T U : Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val) :
    IsPullback
      (Arrows.finiteIntersectionArrow X (S := T) (T := Unions.finiteIntersectionUnion X T U)
        (by classical exact Finset.subset_union_left)).left
      (Arrows.finiteIntersectionArrow X (S := U) (T := Unions.finiteIntersectionUnion X T U)
        (by classical exact Finset.subset_union_right)).left
      (Arrows.finiteIntersectionArrow X hST).left (Arrows.finiteIntersectionArrow X hSU).left := by
  exact isPullback_homOfLE_of_eq_inf
    (Arrows.finiteIntersectionOpen_antitone X (by classical exact Finset.subset_union_left))
    (Arrows.finiteIntersectionOpen_antitone X (by classical exact Finset.subset_union_right))
    (Arrows.finiteIntersectionOpen_antitone X hST) (Arrows.finiteIntersectionOpen_antitone X hSU)
    (Unions.finiteIntersectionOpen_union X T U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Pullbacks
