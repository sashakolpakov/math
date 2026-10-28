import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Abel

/-! # Cubical Bilinear -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CubicalBilinear.Construction

noncomputable section

/-! The cross effect of a normalized cubical function is an actual symmetric bilinear map. -/

universe u v

variable {G : Type u} {P : Type v} [AddCommGroup G] [AddCommGroup P]
  (q : G → P) (hzero : q 0 = 0)
  (hcube : ∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z))

def cubicalCrossEffect (x y : G) : P := q (x + y) - q x - q y

theorem cubicalCrossEffect_symmetric (x y : G) : cubicalCrossEffect q x y = cubicalCrossEffect q y x := by
  unfold cubicalCrossEffect
  rw [add_comm x y]
  abel

include hcube in
theorem cubicalCrossEffect_add_left (x y z : G) :
    cubicalCrossEffect q (x + y) z = cubicalCrossEffect q x z + cubicalCrossEffect q y z := by
  have h := hcube x y z
  have he : q (x + y + z) = q (x + y) + q (x + z) + q (y + z) - q x - q y - q z := by
    apply add_right_cancel (b := q x + q y + q z)
    calc
      _ = q (x + y) + q (x + z) + q (y + z) := by simpa only [add_assoc] using h
      _ = _ := by abel
  unfold cubicalCrossEffect
  rw [he]
  abel

include hcube in
theorem cubicalCrossEffect_add_right (x y z : G) :
    cubicalCrossEffect q x (y + z) = cubicalCrossEffect q x y + cubicalCrossEffect q x z := by
  rw [cubicalCrossEffect_symmetric q x (y + z), cubicalCrossEffect_add_left q hcube,
    cubicalCrossEffect_symmetric q y x, cubicalCrossEffect_symmetric q z x]

def cubicalCrossAddHom : G →+ G →+ P where
  toFun x := {
    toFun := cubicalCrossEffect q x
    map_zero' := by simp [cubicalCrossEffect, hzero]
    map_add' := cubicalCrossEffect_add_right q hcube x }
  map_zero' := by ext x; simp [cubicalCrossEffect, hzero]
  map_add' x y := by ext z; exact cubicalCrossEffect_add_left q hcube x y z

def cubicalCrossBilinear : G →ₗ[ℤ] G →ₗ[ℤ] P where
  toFun x := ((cubicalCrossAddHom q hzero hcube) x).toIntLinearMap
  map_add' x y := by ext z; exact cubicalCrossEffect_add_left q hcube x y z
  map_smul' n x := by
    ext z
    exact congrArg (fun h : G →+ P => h z) ((cubicalCrossAddHom q hzero hcube).map_zsmul n x)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CubicalBilinear.Construction
