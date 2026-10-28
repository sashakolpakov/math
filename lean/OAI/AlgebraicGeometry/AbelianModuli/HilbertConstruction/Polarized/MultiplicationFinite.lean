import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.GeometricFibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.GeometricFiberFiniteness

/-! # Multiplication Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Positive multiplication and torsion on polarized abelian schemes are finite over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.multiplication_isFinite (n : ℕ) (hn : 0 < n) :
    IsFinite (A.abelian.multiplication n).left :=
  Proper.GeometricFiberFiniteness.proper_isFinite_of_geometric_fieldPullbacks (A.abelian.multiplication n).left
    (A.multiplication_geometricFiber_isFinite n hn)

theorem PolarizationData.PolarizedAbelianWithFullLevel.torsionScheme_isFinite_overBase (n : ℕ) (hn : 0 < n) :
    IsFinite (A.abelian.torsionScheme n).hom := by
  have : IsFinite (A.abelian.multiplication n).left := A.multiplication_isFinite n hn
  exact inferInstanceAs (IsFinite (Limits.pullback.snd (A.abelian.multiplication n).left η[A.abelian.scheme].left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
