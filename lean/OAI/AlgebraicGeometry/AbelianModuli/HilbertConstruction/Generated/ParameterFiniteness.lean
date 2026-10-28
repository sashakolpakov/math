import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ParameterProperness
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Parameter Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFiniteness

noncomputable section

/-! Over a locally noetherian base, the generated parameter locus is quasi-compact, separated, and locally of finite presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsLocallyNoetherian S] (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)

theorem truncatedGeneratedInclusion_quasiCompact : QuasiCompact (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left := by
  let M := Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  exact inferInstanceAs (QuasiCompact (Truncated.GenerationOpens.truncatedGeneratedOpen S n B r N).ι)

theorem truncatedGeneratedParameters_quasiCompact : QuasiCompact (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom := by
  have := truncatedGeneratedInclusion_quasiCompact S n B r N
  rw [← (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).w]
  infer_instance

theorem truncatedGeneratedParameters_locallyFinitePresentation :
    LocallyOfFinitePresentation (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom := by
  apply LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
  rw [← (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).w]
  infer_instance

omit [IsLocallyNoetherian S] in
theorem truncatedGeneratedParameters_separated : IsSeparated (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom := by
  rw [← (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).w]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFiniteness
