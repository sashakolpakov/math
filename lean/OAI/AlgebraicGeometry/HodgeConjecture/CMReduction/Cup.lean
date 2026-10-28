import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CycleOperations
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPullback
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegralPresentation
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Cup.CM.Construction

noncomputable section

/-! Closure of genuine cycle-class images under cup product is derived
from the supplied exterior-product and pullback inputs using the diagonal.
No existence-of-intersection or cup-algebraicity premise is added. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory

theorem rational_cup_algebraic_on_presentation
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (X P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (π₁ π₂ : P.toOver ⟶ X.toOver)
    (hprod : IsLimit (BinaryFan.mk π₁ π₂))
    (p q : ℕ) (a : X.rationalCohomology (p + p)) (b : X.rationalCohomology (q + q))
    (ha : a ∈ X.geometricAlgebraicClasses p) (hb : b ∈ X.geometricAlgebraicClasses q) :
    cast (congrArg (fun n => (X.rationalCohomology n : Type))
      (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)
        (p + p) (q + q) a b) ∈ X.geometricAlgebraicClasses (p + q) := by
  let δ : X.toOver ⟶ P.toOver := BinaryFan.IsLimit.lift hprod (𝟙 X.toOver) (𝟙 X.toOver)
  have h₁ : δ ≫ π₁ = 𝟙 X.toOver := BinaryFan.IsLimit.lift_fst hprod _ _
  have h₂ : δ ≫ π₂ = 𝟙 X.toOver := BinaryFan.IsLimit.lift_snd hprod _ _
  have h := CycleOperations.CM.Construction.rational_pullback_algebraic h_LineBundleCycles X P δ (p + q) _
    (CycleOperations.CM.Construction.rational_exterior_product_algebraic h_ThomClass X X P π₁ π₂ hprod p q a b ha hb)
  rw [CupPullback.CM.Construction.scheme_pullback_cast δ (add_add_add_comm p p q q), CupPullback.CM.Construction.scheme_cup_pullback, CupPullback.CM.Construction.scheme_pullback_comp,
    CupPullback.CM.Construction.scheme_pullback_comp, h₁, h₂, CupPullback.CM.Construction.scheme_pullback_id, CupPullback.CM.Construction.scheme_pullback_id] at h
  exact h

/-- The same closure statement for the original integral-variety interface. -/
theorem rational_cup_algebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p q : ℕ) (a : X.rationalCohomology (p + p)) (b : X.rationalCohomology (q + q))
    (ha : a ∈ X.geometricAlgebraicClasses p) (hb : b ∈ X.geometricAlgebraicClasses q) :
    cast (congrArg (fun n => (X.rationalCohomology n : Type))
      (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)
        (p + p) (q + q) a b) ∈ X.geometricAlgebraicClasses (p + q) := by
  rw [← IntegralPresentation.CM.Construction.integral_presentation_geometricClasses X p] at ha
  rw [← IntegralPresentation.CM.Construction.integral_presentation_geometricClasses X q] at hb
  rw [← IntegralPresentation.CM.Construction.integral_presentation_geometricClasses X (p + q)]
  exact rational_cup_algebraic_on_presentation h_LineBundleCycles h_ThomClass X.presentation
    (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation X.presentation X.presentation)
    (fst _ _) (snd _ _) (tensorProductIsBinaryProduct X.toOver X.toOver)
    p q a b ha hb

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Cup.CM.Construction
