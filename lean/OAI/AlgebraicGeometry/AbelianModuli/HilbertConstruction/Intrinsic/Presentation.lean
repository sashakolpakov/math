import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterScheme

/-! # Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Presentation.NativeHilbertAbelianLift

noncomputable section

/-! The original universal Hilbert family's projective presentation,
using its actual closed-family inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (S : Scheme.{u}) (n : ℕ) (H : Polynomial ℚ)

def presentation : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme :=
  ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.inclusion, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Presentation.NativeHilbertAbelianLift
