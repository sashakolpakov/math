import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Unramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication is finite without a polarization assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_isFinite (level : A.FullLevel n) :
    IsFinite (A.multiplication n).left := by
  have := A.fullLevel_multiplication_formallyUnramified level
  have := UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified (A.multiplication n).left
  exact IsFinite.of_isProper_of_locallyQuasiFinite (A.multiplication n).left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
