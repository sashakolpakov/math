import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionFunctor
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Reference Intersection Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionPullbacks

noncomputable section

/-! Every pair of original intersection charts has its union intersection as pullback over the original scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isPullback_opens_of_eq_inf {Y : Scheme.{u}} {A B D : Y.Opens}
    (hA : D ≤ A) (hB : D ≤ B) (hD : D = A ⊓ B) :
    IsPullback (Y.homOfLE hA) (Y.homOfLE hB) A.ι B.ι := by
  subst D
  exact isPullback_opens_inf A B

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

theorem originalIntersection_pair_isPullback (S T : Finite.AffineIntersections.finiteIntersectionIndex X) :
    IsPullback
      (FiniteIntersection.Arrows.finiteIntersectionArrow X (FiniteIntersection.Unions.finiteIntersection_subset_union_left X S T)).left
      (FiniteIntersection.Arrows.finiteIntersectionArrow X (FiniteIntersection.Unions.finiteIntersection_subset_union_right X S T)).left
      (Finite.AffineIntersections.finiteIntersectionOpen X S).ι (Finite.AffineIntersections.finiteIntersectionOpen X T).ι :=
  isPullback_opens_of_eq_inf
    (FiniteIntersection.Arrows.finiteIntersectionOpen_antitone X (FiniteIntersection.Unions.finiteIntersection_subset_union_left X S T))
    (FiniteIntersection.Arrows.finiteIntersectionOpen_antitone X (FiniteIntersection.Unions.finiteIntersection_subset_union_right X S T))
    (FiniteIntersection.Unions.finiteIntersectionOpen_union X S T)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionPullbacks
