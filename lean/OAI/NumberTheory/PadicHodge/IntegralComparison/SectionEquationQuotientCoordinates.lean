import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue

/-! # Section Equation Quotient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotientCoordinates

noncomputable section

/-! The scalar extracted from the original affine point quotient is
literal restriction of the point section to the base, not an arbitrary
isomorphism with the coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  (z : Spec (CommRingCat.of R) ⟶ Y.left) [IsClosedImmersion z]
  (hz : z ≫ Y.hom = 𝟙 _) (U : Y.left.Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ z ⁻¹ᵁ U) {d : ℕ} (a : Fin d → Intrinsic.SmoothClosedSections.ring R Y U)
  (ha : Koszul.OrientedTopCohomology.ideal (Intrinsic.SmoothClosedSections.ring R Y U) a = z.ker.ideal ⟨U,hU⟩)

theorem normalize (x : Γ(Principal.ClosedQuotient.directImage z, U)) :
    SectionEquationQuotient.equiv R Y z hz U hU hcontains a ha
      ((Principal.OrientedResidue.quotientIso z U hU a ha).hom
        ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage z)).hom x)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hcontains).op x) := by
  obtain ⟨r, rfl⟩ := z.app_surjective U hU x
  change SectionEquationQuotient.equiv R Y z hz U hU hcontains a ha
    ((Ideal.quotientEquivAlgOfEq Γ(Y.left, U) ha.symm)
      ((Closed.QuotientSectionNormalization.chartIso z U hU).hom
        ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage z)).hom
          (z.app U r)))) = _
  rw [Closed.QuotientSectionNormalization.chartIso_apply,
    Closed.QuotientSectionNormalization.iso_pullback, Ideal.quotientEquivAlgOfEq_mk]
  exact SectionEquationQuotient.equiv_mk R Y z hz U hU hcontains a ha r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotientCoordinates
