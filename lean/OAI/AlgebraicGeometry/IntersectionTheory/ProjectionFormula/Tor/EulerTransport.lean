import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Symmetry

/-! # Euler Transport -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport

noncomputable section

/-! Isomorphism invariance in the second variable and symmetry of the
native truncated Tor Euler characteristic. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

theorem iso_right (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (e : N ≅ N') (d : ℕ) : Euler.euler R M N d = Euler.euler R M N' d := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun n : ℕ∞ => (-1 : ℚ) ^ i * (n.toNat : ℚ))
    ((((Tor (ModuleCat R) i).obj M).mapIso e).toLinearEquiv.length_eq)

theorem comm (M N : ModuleCat.{u} R) (d : ℕ) :
    Euler.euler R M N d = Euler.euler R N M d := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun n : ℕ∞ => (-1 : ℚ) ^ i * (n.toNat : ℚ))
    (Symmetry.length_comm R M N i)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport
