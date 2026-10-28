import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import Mathlib.AlgebraicGeometry.Limits

/-! # Empty Intrinsic Families -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyIntrinsicFamilies

noncomputable section

/-! Native Hilbert families over an empty test scheme are unique, and
satisfy every exact fiber-polynomial condition vacuously. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem idealSheafData_subsingleton_of_isEmpty (Z : Scheme.{u}) [IsEmpty Z] :
    Subsingleton Z.IdealSheafData := by
  refine ⟨fun I J => ?_⟩
  apply Scheme.IdealSheafData.ext
  funext U
  exact Subsingleton.elim _ _

namespace Hilbert

variable {S : Scheme.{u}} (X : Over S) (T : Over S) [IsEmpty T.left]

theorem ambient_isEmpty : IsEmpty (Hilbert.Functor.ambient X T) :=
  (Hilbert.Functor.ambientProjection X T).base.hom.1.isEmpty

theorem family_subsingleton_of_isEmpty : Subsingleton (Hilbert.Functor.Family X T) := by
  let := ambient_isEmpty X T
  let := idealSheafData_subsingleton_of_isEmpty (Hilbert.Functor.ambient X T)
  exact ⟨fun F G => Subtype.ext (Subsingleton.elim F.val G.val)⟩

def emptyBaseFamily : Hilbert.Functor.Family X T := by
  let I : (Hilbert.Functor.ambient X T).IdealSheafData := ⊥
  let p := Hilbert.Functor.familyProjection X I
  let : IsIso p := inferInstance
  exact ⟨I, inferInstanceAs (Flat p), inferInstanceAs (IsProper p),
    inferInstanceAs (LocallyOfFinitePresentation p)⟩

end Hilbert

namespace Statement

variable {S : Scheme.{u}} {X T : Over S} [IsEmpty T.left]

theorem emptyBaseFamily_hasFiberHilbertPolynomial
    (B : Has.Core.ProjectivePresentation X) (F : Hilbert.Functor.Family X T) (P : Polynomial ℚ) :
    Has.Core.HasFiberHilbertPolynomial B F P := by
  intro K _ a
  exact isEmptyElim (a (IsLocalRing.closedPoint K))

end Statement

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyIntrinsicFamilies
