import OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticMk
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubicalBilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Nonnegative Quadratic Bilinear -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The parallelogram identity supplies the actual bilinear polarization
of each nonnegative quadratic coefficient in the Hilbert filtration. -/

universe u
variable {G : Type u} [AddCommGroup G] (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.cube (x y z : G) :
    q.value (x + y + z) + q.value x + q.value y + q.value z =
      q.value (x + y) + q.value (x + z) + q.value (y + z) := by
  have h₁ := q.parallelogram (x + y) z
  have h₂ := q.parallelogram (x + z) y
  have h₃ := q.parallelogram x (y - z)
  have h₄ := q.parallelogram y z
  have hxyz : x + z + y = x + y + z := by abel
  have hxm : x + z - y = x - (y - z) := by abel
  have hxp : x + (y - z) = x + y - z := by abel
  rw [hxyz, hxm] at h₂
  rw [hxp] at h₃
  linarith

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.bilinear : G →ₗ[ℤ] G →ₗ[ℤ] ℚ := CubicalBilinear.Construction.cubicalCrossBilinear q.value q.zero q.cube

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.bilinear_apply (x y : G) : q.bilinear x y = q.value (x + y) - q.value x - q.value y := rfl

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.bilinear_self (x : G) : q.bilinear x x = 2 * q.value x := by
  have h := q.nsmul 2 x
  rw [two_nsmul] at h
  change q.value (x + x) - q.value x - q.value x = _
  norm_num at h
  linarith

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.zsmul (n : ℤ) (x : G) : q.value (n • x) = (n : ℚ) ^ 2 * q.value x := by
  cases n with
  | ofNat n => simpa using q.nsmul n x
  | negSucc n =>
    rw [negSucc_zsmul, q.neg, q.nsmul]
    push_cast
    ring

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quadraticMap : QuadraticMap ℤ G ℚ where
  toFun := q.value
  toFun_smul n x := by
    rw [q.zsmul]
    simp only [zsmul_eq_mul, Int.cast_mul, pow_two]
  exists_companion' := ⟨q.bilinear, fun x y => by rw [NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.bilinear_apply]; ring⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
