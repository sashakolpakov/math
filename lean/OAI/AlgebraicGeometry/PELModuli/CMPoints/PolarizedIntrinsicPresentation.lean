import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientRealization
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Polarized Intrinsic Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedIntrinsicPresentation

noncomputable section

/-! A geometric presentation of the original polarized complex
abelian scheme, using the same native object as its coefficient Hodge data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def polarizedNativePresentation {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A.abelian where
  variety := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  comparison := (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)).symm
  comparison_group := inferInstanceAs
    (IsMonHom (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)).inv)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedIntrinsicPresentation
