import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleSchemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Finite

/-! # Etale -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication is finite etale over an arbitrary base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_etale (level : A.FullLevel n) : Etale (A.multiplication n).left := by
  have := A.fullLevel_multiplication_formallyUnramified level
  have : SmoothOfRelativeDimension g ((A.multiplication n).left ≫ A.scheme.hom) := by
    rw [(A.multiplication n).w]
    infer_instance
  exact EqualDimensionEtaleSchemes.etale_of_smooth_equal_dimension (A.multiplication n).left A.scheme.hom g

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
