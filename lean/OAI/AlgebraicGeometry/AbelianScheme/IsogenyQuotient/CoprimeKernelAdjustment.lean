import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimePowerRoots

/-! # Coprime Kernel Adjustment -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelAdjustment.Construction

/-! A Bezout adjustment separates a point over a coprime kernel into
an original quotient-kernel part and a complementary-kernel part. -/

universe u v w z
variable {A : Type u} {B : Type v} {C : Type w} {Z : Type z}
  [CommGroup A] [CommGroup B] [Group C] [Group Z]

theorem coprimeKernel_adjustment
    (φ : A →* Z) (f : A →* B) (r : B →* A) (q : B →* C)
    (n d : ℕ) (hnd : n.Coprime d)
    (hfr : ∀ a : A, r (f a) = a ^ n)
    (hφ : ∀ a : A, φ a = 1 → a ^ d = 1)
    (hf : ∀ a : A, φ a = 1 → q (f a) = 1)
    (x : B) (hx : φ (r x) = 1) :
    ∃ a b : B, q a = 1 ∧ r b = 1 ∧ x = a * b := by
  let y := (r x) ^ n.gcdA d
  have hy : φ y = 1 := by dsimp only [y]; rw [map_zpow, hx, one_zpow]
  have hyn : y ^ n = r x := CoprimePowerRoots.Construction.coprimePowerRoot_pow n d hnd (r x) (hφ (r x) hx)
  refine ⟨f y, x / f y, hf y hy, ?_, ?_⟩
  · rw [map_div, hfr, hyn, div_self']
  · rw [← mul_div_assoc, mul_comm (f y) x, mul_div_cancel_right]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelAdjustment.Construction
