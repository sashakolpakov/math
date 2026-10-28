import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality

/-! # Family Descent Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescentUniqueness

noncomputable section

/-! Descent of native Hilbert families is unique because equality of
their actual defining ideal sheaves is local on the ambient open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {T : Over S} {J : Type u}
variable (U : J → Over S) (f : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t)

include hcover in
theorem family_eq_of_openCover (F G : Functor.Family X T)
    (h : ∀ i, Functor.pullbackFamily X (f i) F = Functor.pullbackFamily X (f i) G) : F = G := by
  apply Subtype.ext
  apply AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality.ideal_eq_of_open_cover (AmbientCover.ambientOpenCover X U f hcover)
  intro i
  exact congrArg Subtype.val (h i)

include hcover in
theorem existsUnique_family_descent (F : ∀ i, Functor.Family X (U i))
    (hc : ∀ i j, Functor.pullbackFamily X (pullback.fst (f i) (f j)) (F i) =
      Functor.pullbackFamily X (pullback.snd (f i) (f j)) (F j)) :
    ∃! G : Functor.Family X T, ∀ i, Functor.pullbackFamily X (f i) G = F i := by
  refine ⟨FamilyDescent.descendedFamily X U f hcover F hc, FamilyDescent.descendedFamily_restriction X U f hcover F hc, ?_⟩
  intro G hG
  exact family_eq_of_openCover X U f hcover G _
    (fun i => (hG i).trans (FamilyDescent.descendedFamily_restriction X U f hcover F hc i).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescentUniqueness
