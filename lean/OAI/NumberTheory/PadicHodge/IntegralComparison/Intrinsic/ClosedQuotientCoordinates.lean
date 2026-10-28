import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization

/-! # Closed Quotient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientCoordinates

noncomputable section

/-! The original closed-quotient coordinate is the native pullback
of local functions, also after changing from module to algebra notation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)

theorem inverse (a : SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩) :
    (Closed.QuotientSectionNormalization.iso f.left U hU).inv a =
      SmoothClosedSections.quotientEquiv R X Y f U hU a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Closed.QuotientSectionNormalization.iso_inv_mk f.left U hU x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientCoordinates
