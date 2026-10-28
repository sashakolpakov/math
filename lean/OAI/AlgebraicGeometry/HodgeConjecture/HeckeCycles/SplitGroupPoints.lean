import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Split Group Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupPoints.CM

noncomputable section

/-! A split homomorphism of commutative groups gives an explicit product
of its kernel and its target. This will be applied to every test object
of the constructed finite group-scheme retraction. -/

variable {A B : Type*} [CommGroup A] [CommGroup B]
  (r : A →* B) (s : B →* A) (hrs : ∀ b, r (s b) = b)

def kernelCoordinate (a : A) : r.ker :=
  ⟨a * (s (r a))⁻¹, by
    change r (a * (s (r a))⁻¹) = 1
    rw [map_mul, map_inv, hrs, mul_inv_cancel]⟩

def productEquiv : r.ker × B ≃* A where
  toFun x := x.1.val * s x.2
  invFun a := (kernelCoordinate r s hrs a, r a)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change x.1.val * s x.2 * (s (r (x.1.val * s x.2)))⁻¹ = x.1.val
      have hk : r x.1.val = 1 := x.1.property
      rw [map_mul, hk, hrs, one_mul, mul_inv_cancel_right]
    · change r (x.1.val * s x.2) = x.2
      have hk : r x.1.val = 1 := x.1.property
      rw [map_mul, hk, hrs, one_mul]
  right_inv a := by
    change a * (s (r a))⁻¹ * s (r a) = a
    exact inv_mul_cancel_right a (s (r a))
  map_mul' x y := by
    change (x.1.val * y.1.val) * s (x.2 * y.2) =
      (x.1.val * s x.2) * (y.1.val * s y.2)
    rw [map_mul, mul_mul_mul_comm]

theorem productEquiv_apply (x : r.ker) (b : B) :
    productEquiv r s hrs (x, b) = x.val * s b := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupPoints.CM
