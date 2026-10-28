import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbol
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientCoordinates

/-! # Differential Symbol -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.DifferentialSymbol

noncomputable section

/-! Multiplication by the actual differential symbol sends the
original closed-quotient coefficient to its literal form section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (U : Y.left.Opens) (hU : IsAffineOpen U) (g : ℕ)
  (t : Fin g → Γ(X.left, f.left ⁻¹ᵁ U))

local instance sectionAlgebra : Algebra R Γ(X.left, f.left ⁻¹ᵁ U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (f.left ⁻¹ᵁ U)

theorem sections_quotient
    (a : Intrinsic.SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩) :
    Principal.PushforwardSectionCoordinates.sectionsMap f.left U (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
      (Principal.DifferentialSymbol.generator R X Y f U g t)
      ((QuotientSectionNormalization.iso f.left U hU).inv a) =
    Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U)
        (Intrinsic.SmoothClosedSections.quotientEquiv R X Y f U hU a) t) := by
  change (show Γ(X.left, f.left ⁻¹ᵁ U) from
      (QuotientSectionNormalization.iso f.left U hU).inv a) •
    Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U) 1 t) = _
  rw [Intrinsic.ClosedQuotientCoordinates.inverse,
    ← (Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)).map_smul,
    ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.DifferentialSymbol
