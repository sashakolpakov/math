import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientRestriction

/-! # Closed Form Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormRestriction

noncomputable section

/-! The native closed-form section isomorphisms are independent of
étale coordinates and commute with the actual ideal-quotient restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (U : Y.left.Opens) (hU : IsAffineOpen U)
  (σ : Type u) [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]

theorem coordinate_independent (τ : Type u) [LinearOrder τ]
    [Algebra (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
    [IsScalarTower R (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
    [Algebra.Etale (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))] (n : ℕ) :
    ClosedFormSections.iso R X Y f U hU σ n = ClosedFormSections.iso R X Y f U hU τ n := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro ω
  exact congrArg (fun e => e.symm
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (ClosedFormSections.quotientIso R X Y f U hU).hom n ω))
    (IntegralComparison.Etale.FormSections.Integral.exteriorIso_chart_independent R X (f.left ⁻¹ᵁ U)
      (hU.preimage f.left) σ τ n)

variable (V : Y.left.Opens) (hV : IsAffineOpen V)
  (τ : Type u) [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V))]
  [IsScalarTower R (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V))]
  [Algebra.Etale (MvPolynomial τ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V))]

theorem restriction (i : V ⟶ U) (n : ℕ)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (ClosedFormSections.quotient R X Y f U hU) n) :
    (ClosedFormSections.directImage R X Y f n).presheaf.map i.op ((ClosedFormSections.iso R X Y f U hU σ n).hom ω) =
      (ClosedFormSections.iso R X Y f V hV τ n).hom
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (ClosedQuotientRestriction.map R X Y f U V hU hV i) n ω) := by
  exact (IntegralComparison.Etale.FormSections.Integral.exteriorIso_symm_restriction R X (f.left ⁻¹ᵁ U)
    (hU.preimage f.left) σ (f.left ⁻¹ᵁ V) (hV.preimage f.left) τ
    ((Opens.map f.left.base).map i) n
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (ClosedFormSections.quotientIso R X Y f U hU).hom n ω)).trans
      (congrArg (IntegralComparison.Etale.FormSections.Integral.exteriorIso R X (f.left ⁻¹ᵁ V)
        (hV.preimage f.left) τ n).symm
        (ClosedQuotientRestriction.forms R X Y f U V hU hV i n ω))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormRestriction
