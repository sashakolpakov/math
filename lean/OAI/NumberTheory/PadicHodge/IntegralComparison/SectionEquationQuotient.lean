import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

/-! # Section Equation Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotient

noncomputable section

/-! Any actual equations for a section contained in an affine open
have the canonical base-ring quotient, given by section evaluation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  (z : Spec (CommRingCat.of R) ⟶ Y.left) [IsClosedImmersion z]
  (hz : z ≫ Y.hom = 𝟙 _) (U : Y.left.Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ z ⁻¹ᵁ U) {d : ℕ} (a : Fin d → Intrinsic.SmoothClosedSections.ring R Y U)
  (ha : Koszul.OrientedTopCohomology.ideal (Intrinsic.SmoothClosedSections.ring R Y U) a = z.ker.ideal ⟨U,hU⟩)

 def equiv : (Intrinsic.SmoothClosedSections.ring R Y U ⧸ Koszul.OrientedTopCohomology.ideal (Intrinsic.SmoothClosedSections.ring R Y U) a) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (ha.trans
    (Intrinsic.SectionEvaluation.kernel R Y z hz U hcontains hU).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains)
      (fun r => ⟨algebraMap R (Intrinsic.SmoothClosedSections.ring R Y U) r,
        (Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains).commutes r⟩))

 theorem equiv_mk (r : Intrinsic.SmoothClosedSections.ring R Y U) :
    equiv R Y z hz U hU hcontains a ha (Ideal.Quotient.mk _ r) =
      Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains r := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotient
