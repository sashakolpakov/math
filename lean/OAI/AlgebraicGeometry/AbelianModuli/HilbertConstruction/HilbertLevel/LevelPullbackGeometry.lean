import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveFiberProducts

/-! # Level Pullback Geometry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.LevelPullbackGeometry.HilbertLevelPullback

noncomputable section

/-! The bounded full-level Hilbert parameter pulled back to a
quasi-projective chart has an actual quasi-projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (Z : Over S) (c : Z ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)

def quasiProjective (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation Z) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c) := by
  letI : IsSeparated (Hilbert.ParameterScheme.hilbertParameterScheme S n P).hom :=
    (Hilbert.ParameterScheme.hilbertParameterQuasiProjectivePresentation S n P).separated
  exact Q.fiberProduct (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelQuasiProjectivePresentation S n P g Pm Pi N)
    c (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.LevelPullbackGeometry.HilbertLevelPullback
