import Mathlib.Algebra.Group.Basic

/-! # Cocycle Square Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CocycleSquareSymmetry

/-! The square of a normalized scalar two-cocycle is symmetric on
elements of order dividing two. This is the scalar obstruction needed
for descending a squared line bundle through two-torsion. -/

theorem cocycle_square_symmetric_of_involution
    {G U : Type*} [CommMonoid G] [CancelCommMonoid U]
    (c : G → G → U) (hleft : ∀ a, c 1 a = 1) (hright : ∀ a, c a 1 = 1)
    (hc : ∀ a b d, c (a * b) d * c a b = c a (b * d) * c b d)
    (a b : G) (ha : a * a = 1) : c a b ^ 2 = c b a ^ 2 := by
  have h₁ : c a (a * b) * c a b = c a a := by
    simpa only [ha, hleft b, one_mul] using (hc a a b).symm
  have h₂ : c (a * b) a * c a b = c a (a * b) * c b a := by
    simpa only [mul_comm b a] using hc a b a
  have h₃ : c (a * b) a * c b a = c a a := by
    simpa only [mul_comm b a, ha, hright b, one_mul] using hc b a a
  apply mul_left_cancel (a := c (a * b) a)
  calc
    c (a * b) a * c a b ^ 2 = (c (a * b) a * c a b) * c a b := by
      rw [pow_two, mul_assoc]
    _ = (c a (a * b) * c b a) * c a b := congrArg (fun z => z * c a b) h₂
    _ = (c a (a * b) * c a b) * c b a := by ac_rfl
    _ = c a a * c b a := congrArg (fun z => z * c b a) h₁
    _ = (c (a * b) a * c b a) * c b a := congrArg (fun z => z * c b a) h₃.symm
    _ = c (a * b) a * c b a ^ 2 := by rw [pow_two, mul_assoc]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CocycleSquareSymmetry
