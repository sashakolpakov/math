import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.DualMapFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Isomorphism Dual Determination -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! Poincare compatibility determines the dual component of any complete moduli isomorphism over an arbitrary base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem Isomorphisms.LevelPreservingIso.dual_hom_eq_of_poincare
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : Isomorphisms.LevelPreservingIso A B)
    (d : A.dual.abelian.scheme ⟶ B.dual.abelian.scheme)
    (h : Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ e.abelian.hom).left
      (Line.Bundles.LineBundle.classOf B.dual.poincare) = Line.Bundles.LineBundle.classOf A.dual.poincare) : e.dual.hom = d :=
  B.dual.dualMap_eq_of_poincare_and_familyIso e.abelian e.dual.hom d (e.poincare.trans h.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
