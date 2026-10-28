import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport

/-! # Compatible Transport Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Restrict the constructed compatible transport to a smaller actual
open neighborhood, retaining every original marking equation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.restrict (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F) (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C))
    (hU : IsOpen U) (hx : Intrinsic.FamilyFrames.familyChartCenter C ∈ U) (h : U ⊆ D.neighborhood) :
    Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F where
  neighborhood := U
  isOpen := hU
  center := hx
  subset_frame := h.trans D.subset_frame
  subset_chart := h.trans D.subset_chart
  polarization z v w := D.polarization ⟨z.val, h z.property⟩ v w
  field z a v := D.field ⟨z.val, h z.property⟩ a v
  level z a := D.level ⟨z.val, h z.property⟩ a

end

end OAI.RepresentationTheory.Theta.Geometric
