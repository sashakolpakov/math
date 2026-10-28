import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairBilinearity

/-! # Pair Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Poincare pairing on actual bundle isomorphism classes, including powers and simultaneous inverses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (T : Over (Spec (.of K)))

def Dual.Data.DualAbelianData.poincarePairClass : (T ⟶ D.abelian.scheme) →* ((T ⟶ A.scheme) →* Line.Bundles.LineBundle.IsoClass T.left) where
  toFun f :=
    { toFun := fun a => Line.Bundles.LineBundle.classOf (D.poincarePair f a)
      map_one' := Quotient.sound ⟨D.poincarePair_one_right f⟩
      map_mul' := fun a b => Quotient.sound (D.poincarePair_mul_right f a b) }
  map_one' := by
    ext a
    exact Quotient.sound ⟨D.poincarePair_one_left a⟩
  map_mul' f h := by
    ext a
    exact Quotient.sound (D.poincarePair_mul_left f h a)

theorem Dual.Data.DualAbelianData.poincarePairClass_pow (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (m n : ℕ) :
    Line.Bundles.LineBundle.classOf (D.poincarePair (f ^ m) (a ^ n)) =
      Line.Bundles.LineBundle.classOf (D.poincarePair f a) ^ (m * n) := by
  change D.poincarePairClass T (f ^ m) (a ^ n) = D.poincarePairClass T f a ^ (m * n)
  rw [(D.poincarePairClass T).map_pow]
  change (D.poincarePairClass T f (a ^ n)) ^ m = _
  rw [(D.poincarePairClass T f).map_pow, ← pow_mul, Nat.mul_comm]

theorem Dual.Data.DualAbelianData.poincarePairClass_inv_inv (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf (D.poincarePair f⁻¹ a⁻¹) = Line.Bundles.LineBundle.classOf (D.poincarePair f a) := by
  let B := D.poincarePairClass T
  have h₁ : B f a * B f a⁻¹ = 1 := by
    rw [← (B f).map_mul, mul_inv_cancel, (B f).map_one]
  have h₂ : B f a⁻¹ * B f⁻¹ a⁻¹ = 1 := by
    rw [← MonoidHom.mul_apply, ← B.map_mul, mul_inv_cancel, B.map_one]
    rfl
  exact (calc
    B f⁻¹ a⁻¹ = 1 * B f⁻¹ a⁻¹ := (one_mul _).symm
    _ = (B f a * B f a⁻¹) * B f⁻¹ a⁻¹ := congrArg (fun z => z * B f⁻¹ a⁻¹) h₁.symm
    _ = B f a * (B f a⁻¹ * B f⁻¹ a⁻¹) := mul_assoc _ _ _
    _ = B f a * 1 := congrArg (fun z => B f a * z) h₂
    _ = B f a := mul_one _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
