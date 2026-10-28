import OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski
import OAI.NumberTheory.ArithmeticGroups.Lattices.IdentityComponent

/-! # Semisimple Center -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleCenter.Construction

noncomputable section

/-! Finiteness of the geometric center from the specified semisimplicity. -/

open _root_.TopologicalSpace

theorem semisimple_geometric_center_finite
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hG : G.IsSemisimple) : Finite (Subgroup.center G.GeometricPoints) := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : SeparatelyContinuousMul G.GeometricPoints := {
    continuous_const_mul := fun {g} => Zariski.Construction.geometric_left_mul_continuous G g
    continuous_mul_const := fun {g} => Zariski.Construction.geometric_right_mul_continuous G g }
  let : ContinuousInv G.GeometricPoints := ⟨Zariski.Construction.geometric_inv_continuous G⟩
  let : NoetherianSpace G.GeometricPoints := Zariski.Construction.geometric_noetherian G
  exact IdentityComponent.Construction.finite_center_of_trivial_connected_normal_solvable (Zariski.Construction.geometric_center_closed G) hG

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleCenter.Construction
