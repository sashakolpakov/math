import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Forms

/-! # Coefficient Action -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CoefficientAction

noncomputable section

/-! The usual regular coefficient action on the preserved algebraic symbol quotient. -/

variable (A : Type) [CommRing A] [Algebra ℂ A]

instance formCoefficientSMul (n : ℕ) : SMul A (Forms.Form A n) where
  smul c a := (Exterior.Forms.exteriorFormsEquiv A n).symm (c • Exterior.Forms.exteriorFormsEquiv A n a)

theorem exteriorFormsEquiv_coefficient_smul (n : ℕ) (c : A) (a : Forms.Form A n) :
    Exterior.Forms.exteriorFormsEquiv A n (c • a) = c • Exterior.Forms.exteriorFormsEquiv A n a :=
  (Exterior.Forms.exteriorFormsEquiv A n).apply_symm_apply _

instance formCoefficientModule (n : ℕ) : Module A (Forms.Form A n) :=
  Function.Injective.module A (Exterior.Forms.exteriorFormsEquiv A n).toLinearMap.toAddMonoidHom
    (Exterior.Forms.exteriorFormsEquiv A n).injective (exteriorFormsEquiv_coefficient_smul A n)

instance formCoefficientSmulComm (n : ℕ) : SMulCommClass A ℂ (Forms.Form A n) where
  smul_comm c z a := by
    apply (Exterior.Forms.exteriorFormsEquiv A n).injective
    simp only [exteriorFormsEquiv_coefficient_smul, map_smul]
    exact smul_comm c z _

instance formCoefficientScalarTower (n : ℕ) : IsScalarTower ℂ A (Forms.Form A n) where
  smul_assoc z c a := by
    apply (Exterior.Forms.exteriorFormsEquiv A n).injective
    simp only [exteriorFormsEquiv_coefficient_smul, map_smul]
    exact smul_assoc z c _

def exteriorFormsCoefficientEquiv (n : ℕ) : Forms.Form A n ≃ₗ[A] ⋀[A]^n Ω[A⁄ℂ] where
  toFun := Exterior.Forms.exteriorFormsEquiv A n
  invFun := (Exterior.Forms.exteriorFormsEquiv A n).symm
  left_inv := (Exterior.Forms.exteriorFormsEquiv A n).left_inv
  right_inv := (Exterior.Forms.exteriorFormsEquiv A n).right_inv
  map_add' := (Exterior.Forms.exteriorFormsEquiv A n).map_add
  map_smul' := exteriorFormsEquiv_coefficient_smul A n

theorem coefficient_smul_formSymbol (n : ℕ) (c : A) (a : Fin (n + 1) → A) :
    c • Forms.formSymbol A a = Forms.formSymbol A (Function.update a 0 (c * a 0)) := by
  apply (Exterior.Forms.exteriorFormsEquiv A n).injective
  simp only [exteriorFormsEquiv_coefficient_smul, Exterior.Forms.exteriorFormsEquiv_symbol,
    Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _), mul_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CoefficientAction
