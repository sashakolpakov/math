import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Ample
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity

noncomputable section

/-! Polarization positivity supplies an actual projective embedding of
the original complex abelian scheme. No projective presentation is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} {δ : Fin g → ℕ} {N : ℕ}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The polarization's ample bundle embeds the actual abelian scheme in
relative projective space over the same complex base. -/
def polarizedProjectivePresentation : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme := by
  let L := Classical.choose (Polarization.Ample.polarization_has_ample_line_bundle A)
  have hL : L.IsAmple := Classical.choose_spec (Polarization.Ample.polarization_has_ample_line_bundle A)
  exact hL.projectivePresentation A.abelian.scheme.hom

/-- The native complex projective embedding constructed from the polarization. -/
def polarizedNativeProjectivePresentation :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation A.abelian.scheme.left A.abelian.scheme.hom :=
  Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation (polarizedProjectivePresentation A)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity
