import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UniversalBaseChange

/-! # Classification Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassificationTransport

noncomputable section

/-! Unique classification by a relative family is preserved when the ambient parameter is rewritten by an equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem hilbertClassifier_existsUnique_of_eq
    {S : Scheme.{u}} {T M M' : Over S} {n : ℕ} {P : Polynomial ℚ}
    (hM : M = M') (U : RelativeProjective.Families.RelativeProjectiveHilbertFamily M'.left n P)
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P)
    (h : ∃! g : T ⟶ M', U.pullback g.left = F) :
    ∃! g : T ⟶ M,
      (Eq.mpr (congrArg (fun Z : Over S => RelativeProjective.Families.RelativeProjectiveHilbertFamily Z.left n P) hM) U).pullback g.left = F := by
  subst M'
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassificationTransport
