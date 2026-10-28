import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.AffineLiftingEq
import Mathlib.Tactic.LinearCombination

/-! # Infinitesimal Roots In -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalRootsIn.InfinitesimalRoots

/-!
# TorsionQuotient: division by m in the infinitesimal identity kernel

Affine interpolation between algebra maps is again an algebra map when
their difference lies in a square-zero ideal. Interpolating a character
with the identity by 1/m constructs its infinitesimal m-th root.
-/

open _root_.Algebra Coalgebra WithConv

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]

/-- Actual interpolation of algebra maps across a square-zero ideal. -/
def interpolateAlgHom [Algebra R B] [Algebra R C]
    (J : Ideal C) (hJ : J ^ 2 = ⊥) (e f : B →ₐ[R] C)
    (hf : ∀ b, f b - e b ∈ J) (c : C) : B →ₐ[R] C where
  toFun b := e b + c * (f b - e b)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp only [map_add]; ring
  map_mul' x y := by
    have hz := InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal J hJ (hf x) (hf y)
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hz
  commutes' r := by simp only [e.commutes, f.commutes, sub_self, mul_zero, add_zero]

variable [HopfAlgebra R B] [IsCocomm R B] [Algebra R C]

/-- Multiplication by a base unit is surjective on first-order points at
the identity, with a root constructed by interpolation. -/
theorem exists_root_in_identity_kernel
    (J : Ideal C) (hJ : J ^ 2 = ⊥) (f : WithConv (B →ₐ[R] C))
    (hf : ∀ b, f b - algebraMap R C (counit (R := R) b) ∈ J)
    (m : ℕ) (hm : IsUnit (m : C)) :
    ∃ g : WithConv (B →ₐ[R] C), g ^ m = f ∧
      ∀ b, g b - algebraMap R C (counit (R := R) b) ∈ J := by
  obtain ⟨u, hu⟩ := hm
  let e : B →ₐ[R] C := (1 : WithConv (B →ₐ[R] C)).ofConv
  let g := toConv (interpolateAlgHom J hJ e f.ofConv hf (↑u⁻¹ : C))
  have heval : ∀ b, g b = e b + (↑u⁻¹ : C) * (f b - e b) := fun _ => rfl
  have hg : ∀ b, g b - algebraMap R C (counit (R := R) b) ∈ J := by
    intro b
    change g b - e b ∈ J
    rw [heval, add_sub_cancel_left]
    exact J.mul_mem_left _ (hf b)
  refine ⟨g, ?_, hg⟩
  ext b
  rw [InfinitesimalEq.Infinitesimal.character_power_apply J hJ g hg m b]
  change e b + (m : C) * (g b - e b) = f b
  rw [heval, add_sub_cancel_left, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  exact add_sub_cancel _ _

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalRootsIn.InfinitesimalRoots
