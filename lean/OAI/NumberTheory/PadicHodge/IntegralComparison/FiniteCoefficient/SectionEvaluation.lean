import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.PointCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointScalarEvaluation

/-! # Section Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.SectionEvaluation

noncomputable section

/-! The weight in the genuine finite-coefficient point fraction is
the literal value of the coefficient section at the original section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (R : Type u) [CommRing R] (A : Over (Spec (CommRingCat.of R)))
  {Y X : Scheme.{u}} (s₀ : Spec (CommRingCat.of R) ⟶ Y) (f : Y ⟶ X) (i : X ⟶ A.left)
  [IsClosedImmersion i] [IsClosedImmersion ((s₀ ≫ f) ≫ i)]
  (hz : ((s₀ ≫ f) ≫ i) ≫ A.hom = 𝟙 _)
  (U : A.left.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ ((s₀ ≫ f) ≫ i) ⁻¹ᵁ U)
  {c m : ℕ} (s : Fin c → Intrinsic.SmoothClosedSections.ring R A U) (t : Fin m → Intrinsic.SmoothClosedSections.ring R A U)
  (hst : KoszulPartial.Resolution.pointIdeal (Intrinsic.SmoothClosedSections.ring R A U) s t = ((s₀ ≫ f) ≫ i).ker.ideal ⟨U,hU⟩)

omit [IsClosedImmersion i] in
theorem evaluation (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    Closed.PointScalarEvaluation.quotient R A (s₀ ≫ f) i hz U hU hcontains s t hst
      (PointCoordinates.coefficient s₀ f i U hU s t hst x) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (s₀.appLE (f ⁻¹ᵁ (i ⁻¹ᵁ U)) ⊤ hcontains x) := by
  rw [PointCoordinates.evaluation]
  exact Closed.PointScalarEvaluation.normalize R A (s₀ ≫ f) i hz U hU hcontains s t hst
    (s₀.app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.SectionEvaluation
