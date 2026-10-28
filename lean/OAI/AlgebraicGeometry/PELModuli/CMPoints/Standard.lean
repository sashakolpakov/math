import OAI.AlgebraicGeometry.PELModuli.CMPoints.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Standard -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Standard

noncomputable section

/-! Actual polarization positivity now supplies the projective complex
fiber presentations required by CMAbelianVariety. No presentation is an extra input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def standardModuliOfArithmetic (M : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli) : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.StandardAbelianModuli where
  toArithmeticAbelianModuli := M
  complexFiber p := by
    let A := M.universal.polarized.abelian.pullback p
    let P := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
      (M.universal.polarized.geometricFiber_projectivePresentation ℂ p)
    exact {
      variety := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P
      comparison := (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).symm
      comparison_group := inferInstanceAs
        (IsMonHom (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv) }

theorem standardModuliOfArithmetic_carrier (M : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) :
    ((standardModuliOfArithmetic M).abelianAt p).toOver.left =
      (M.universal.polarized.abelian.pullback p).scheme.left := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Standard
