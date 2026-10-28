import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotient

/-! # Section Ideal Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealQuotient

noncomputable section

/-! The quotient by the actual ideal of a section, independent of
any chosen equations, is canonically its base ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  (z : Spec (CommRingCat.of R) ⟶ Y.left) [IsClosedImmersion z]
  (hz : z ≫ Y.hom = 𝟙 _) (U : Y.left.Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ z ⁻¹ᵁ U)

def equiv : (Intrinsic.SmoothClosedSections.ring R Y U ⧸ z.ker.ideal ⟨U, hU⟩) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R
    (Intrinsic.SectionEvaluation.kernel R Y z hz U hcontains hU).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains)
      (fun r => ⟨algebraMap R (Intrinsic.SmoothClosedSections.ring R Y U) r,
        (Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains).commutes r⟩))

theorem equiv_mk (a : Intrinsic.SmoothClosedSections.ring R Y U) :
    equiv R Y z hz U hU hcontains (Ideal.Quotient.mk _ a) =
      Intrinsic.SectionEvaluation.evaluation R Y z hz U hcontains a := rfl

theorem equations {d : ℕ} (a : Fin d → Intrinsic.SmoothClosedSections.ring R Y U)
    (ha : Koszul.OrientedTopCohomology.ideal (Intrinsic.SmoothClosedSections.ring R Y U) a = z.ker.ideal ⟨U, hU⟩) :
    SectionEquationQuotient.equiv R Y z hz U hU hcontains a ha =
      (Ideal.quotientEquivAlgOfEq R ha).trans (equiv R Y z hz U hU hcontains) := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealQuotient
