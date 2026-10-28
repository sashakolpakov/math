import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.TensorFormula

/-! # Class Monoid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.ClassMonoid

noncomputable section

/-! Graph bundle classes form a monoid homomorphism, so opposite dual-valued maps give tensor inverses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

def poincareGraphClassHom (D : Dual.Data.DualAbelianData A) :
    (A.scheme ⟶ D.abelian.scheme) →* Line.Bundles.LineBundle.IsoClass A.scheme.left where
  toFun p := Line.Bundles.LineBundle.classOf (Bundles.poincareGraphBundle D p)
  map_one' := Quotient.sound ⟨TensorFormula.poincareGraphBundle_oneIso D⟩
  map_mul' p q := Quotient.sound (TensorFormula.poincareGraphBundle_mul_iso D p q)

theorem poincareGraphBundle_inverse_tensor (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) :
    Nonempty (((Bundles.poincareGraphBundle D p).tensor (Bundles.poincareGraphBundle D p⁻¹)).sheaf ≅
      Line.Bundles.structureModule A.scheme.left) := by
  have h : poincareGraphClassHom D p * poincareGraphClassHom D p⁻¹ = 1 := by
    rw [← (poincareGraphClassHom D).map_mul, mul_inv_cancel, (poincareGraphClassHom D).map_one]
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.ClassMonoid
