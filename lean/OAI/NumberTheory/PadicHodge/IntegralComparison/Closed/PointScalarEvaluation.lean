import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SectionQuotient

/-! # Point Scalar Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointScalarEvaluation

noncomputable section

/-! The fixed iterated point direct image and the product-basis point
quotient extract the literal value on the original base section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  {X : Scheme.{u}} (s₀ : Spec (CommRingCat.of R) ⟶ X) (f : X ⟶ Y.left)
  [IsClosedImmersion f] [IsClosedImmersion (s₀ ≫ f)]
  (hz : (s₀ ≫ f) ≫ Y.hom = 𝟙 _) (U : Y.left.Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ f) ⁻¹ᵁ U) {c m : ℕ}
  (s : Fin c → Intrinsic.SmoothClosedSections.ring R Y U) (t : Fin m → Intrinsic.SmoothClosedSections.ring R Y U)
  (hst : KoszulPartial.Resolution.pointIdeal (Intrinsic.SmoothClosedSections.ring R Y U) s t = (s₀ ≫ f).ker.ideal ⟨U,hU⟩)

def quotient : ((Intrinsic.SmoothClosedSections.ring R Y U) ⧸ KoszulPartial.Resolution.pointIdeal (Intrinsic.SmoothClosedSections.ring R Y U) s t) ≃ₐ[R] R :=
  KoszulPoint.SectionQuotient.equiv R (Intrinsic.SmoothClosedSections.ring R Y U) s t
    (SectionEquationQuotient.equiv R Y (s₀ ≫ f) hz U hU hcontains (Fin.append s t)
      ((KoszulPoint.Ideal.append _ s t).symm.trans hst))

omit [IsClosedImmersion f] in
theorem quotient_mk (a : Intrinsic.SmoothClosedSections.ring R Y U) :
    quotient R Y s₀ f hz U hU hcontains s t hst (Ideal.Quotient.mk _ a) =
      Intrinsic.SectionEvaluation.evaluation R Y (s₀ ≫ f) hz U hcontains a := by
  exact (KoszulPoint.SectionQuotient.equiv_mk R (Intrinsic.SmoothClosedSections.ring R Y U) s t _ a).trans
    (SectionEquationQuotient.equiv_mk R Y (s₀ ≫ f) hz U hU hcontains (Fin.append s t)
      ((KoszulPoint.Ideal.append _ s t).symm.trans hst) a)

omit [IsClosedImmersion f] in
theorem normalize (x : Γ(Cech.StructurePullbackUnit.coefficients s₀ f, U)) :
    quotient R Y s₀ f hz U hU hcontains s t hst
      ((PointQuotientSquare.pointQuotient s₀ f U hU s t hst).hom
        ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom x)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hcontains).op x) := by
  obtain ⟨a, rfl⟩ := (s₀ ≫ f).app_surjective U hU x
  rw [PointQuotientSquare.pointQuotient_pullback]
  exact quotient_mk R Y s₀ f hz U hU hcontains s t hst a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointScalarEvaluation
