import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Surjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalars
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual finite etale isogeny supplied by multiplication at full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelMultiplicationIsogeny (level : A.FullLevel n) : Abelian.Schemes.AbelianScheme.Isogeny A A where
  hom := A.multiplication n
  preservesGroup := by
    rw [← A.endRing_natCast_hom n]
    infer_instance
  finite := A.fullLevel_multiplication_isFinite level
  flat := by
    have := A.fullLevel_multiplication_etale level
    infer_instance
  surjective := A.fullLevel_multiplication_surjective level

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_effectiveEpi (level : A.FullLevel n) :
    EffectiveEpi (A.multiplication n).left := by
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_surjective level
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
