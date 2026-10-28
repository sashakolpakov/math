import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections

/-! # Closed Form Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSymbols.IntrinsicSections

noncomputable section

/-! The original quotient-to-sheaf comparison sends a differential
symbol to its literal pullback symbol on the closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)
  (σ : Type u) [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

theorem iso_symbol (n : ℕ) (a : ClosedFormSections.quotient R X Y f U hU)
    (v : Fin n → ClosedFormSections.quotient R X Y f U hU) :
    (ClosedFormSections.iso R X Y f U hU σ n).hom
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (ClosedFormSections.quotient R X Y f U hU) n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (ClosedFormSections.quotient R X Y f U hU) a v)) =
    Integral.FormSectionUnit.unit R X n (f.left ⁻¹ᵁ U)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
        (SmoothClosedSections.quotientEquiv R X Y f U hU a)
        (fun i => SmoothClosedSections.quotientEquiv R X Y f U hU (v i))) := by
  apply (IntegralComparison.Etale.FormSections.Integral.exteriorIso R X (f.left ⁻¹ᵁ U)
    (hU.preimage f.left) σ n).injective
  rw [ClosedFormSections.iso_apply, LinearEquiv.apply_symm_apply,
    IntegralComparison.Etale.FormSections.Integral.exteriorIso_unit,
    ← AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.toExterior_natural, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSymbols.IntrinsicSections
