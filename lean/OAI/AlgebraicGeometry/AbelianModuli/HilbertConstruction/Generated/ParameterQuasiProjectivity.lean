import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveImmersions

/-! # Parameter Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterQuasiProjectivity

noncomputable section

/-! The generated finite parameter scheme has an actual quasi-projective presentation over every base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ) (hN : N ≤ B)

def truncatedGeneratedQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N) := by
  letI := GrassmannImmersion.truncatedGeneratedDegreeProjection_isImmersion S n B r N hN
  letI := GrassmannImmersion.truncatedGeneratedDegreeProjection_quasiCompact S n B r N hN
  exact (Homogeneous.QuotientParameters.homogeneousQuotientProjectivePresentation.{u, 0} (Fin (n + 1)) N (r N) S).quasiProjectiveImmersion
    (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN)

include hN in
theorem truncatedGeneratedParameters_quasiCompact_of_degree_le :
    QuasiCompact (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom :=
  (truncatedGeneratedQuasiProjectivePresentation S n B r N hN).quasiCompact

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterQuasiProjectivity
