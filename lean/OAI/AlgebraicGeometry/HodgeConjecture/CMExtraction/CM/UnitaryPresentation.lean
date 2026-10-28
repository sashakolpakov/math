import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuadraticCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv
import OAI.Geometry.ComplexBall.IntegralLattice

/-! # Unitary Presentation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation.Quadratic

noncomputable section

/-! An actual invertible Hermitian matrix over the quadratic presentation
of the CM field, and the entrywise identification of its special unitary
group with the native rational group. -/

open _root_.NumberField
open scoped Classical

section Diagonal
variable {R : Type*} [CommRing R]

def diagonalFormUnit (b : Rˣ) : (Matrix (Fin 3) (Fin 3) R)ˣ where
  val := UnitaryMatrixEquiv.Quadratic.diagonalForm b.val
  inv := UnitaryMatrixEquiv.Quadratic.diagonalForm (b⁻¹).val
  val_inv := by
    simp only [UnitaryMatrixEquiv.Quadratic.diagonalForm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    unfold Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient
    split_ifs <;> simp
  inv_val := by
    simp only [UnitaryMatrixEquiv.Quadratic.diagonalForm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    unfold Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient
    split_ifs <;> simp

end Diagonal

def unitaryFormCongr {R : Type*} [CommRing R] [StarRing R]
    (H K : Matrix (Fin 3) (Fin 3) R) (h : H = K) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU K where
  toFun g := ⟨g.val, h ▸ g.property⟩
  invFun g := ⟨g.val, h.symm ▸ g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (E : Type) [Field E] [NumberField E] [IsCMField E]
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

abbrev quadraticCoefficient : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (QuadraticCoordinates.realBase E) (QuadraticCoordinates.squareParameter E δ hδ) :=
  algebraMap (QuadraticCoordinates.realBase E) _ (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)

theorem quadraticCoefficient_evaluation :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (quadraticCoefficient E b hb δ hδ) = b :=
  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).commutes (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)

def quadraticCoefficientUnit : (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (QuadraticCoordinates.realBase E) (QuadraticCoordinates.squareParameter E δ hδ))ˣ :=
  Units.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.toRingHom.toMonoidHom (Units.mk0 b hb0)

theorem quadraticCoefficientUnit_val :
    (quadraticCoefficientUnit E b hb0 δ hδ hδ0).val = quadraticCoefficient E b hb δ hδ := by
  apply (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).injective
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm b) = _
  rw [AlgEquiv.apply_symm_apply, quadraticCoefficient_evaluation]

def hermitianUnit : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (QuadraticCoordinates.realBase E) (QuadraticCoordinates.squareParameter E δ hδ)))ˣ :=
  diagonalFormUnit (quadraticCoefficientUnit E b hb0 δ hδ hδ0)

theorem hermitianUnit_val :
    (hermitianUnit E b hb0 δ hδ hδ0).val = UnitaryMatrixEquiv.Quadratic.diagonalForm (quadraticCoefficient E b hb δ hδ) := by
  change UnitaryMatrixEquiv.Quadratic.diagonalForm (quadraticCoefficientUnit E b hb0 δ hδ hδ0).val = _
  rw [quadraticCoefficientUnit_val E b hb hb0]

include hb in
theorem hermitianUnit_conjTranspose :
    (hermitianUnit E b hb0 δ hδ hδ0).val.conjTranspose =
      (hermitianUnit E b hb0 δ hδ hδ0).val := by
  rw [hermitianUnit_val E b hb hb0]
  have hc : star (quadraticCoefficient E b hb δ hδ) = quadraticCoefficient E b hb δ hδ := by
    apply (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).injective
    exact (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.quadraticEquiv_star δ hδ hδ0 (quadraticCoefficient E b hb δ hδ)).trans
      ((congrArg (IsCMField.complexConj E) (quadraticCoefficient_evaluation E b hb δ hδ hδ0)).trans
        (hb.trans (quadraticCoefficient_evaluation E b hb δ hδ hδ0).symm))
  apply Matrix.ext
  intro i j
  simp only [UnitaryMatrixEquiv.Quadratic.diagonalForm, Matrix.conjTranspose_apply, Matrix.diagonal, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 2 <;> simp [hi, hc]
  · simp [hij, Ne.symm hij]

def rationalUnitaryPresentation :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (quadraticCoefficient E b hb δ hδ)) :=
  (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.rationalQuadraticUnitaryEquiv b hb δ hδ hδ0).symm.trans
    (UnitaryMatrixEquiv.Quadratic.unitaryMatrixEquiv (quadraticCoefficient E b hb δ hδ))

theorem rationalUnitaryPresentation_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    (rationalUnitaryPresentation E b hb δ hδ hδ0 g).val.val =
      g.val.val.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm :=
  Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.rationalQuadraticUnitaryEquiv_symm_matrix b hb δ hδ hδ0 g

def rationalHermitianUnitaryPresentation :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (hermitianUnit E b hb0 δ hδ hδ0).val :=
  (rationalUnitaryPresentation E b hb δ hδ hδ0).trans
    (unitaryFormCongr _ _ (hermitianUnit_val E b hb hb0 δ hδ hδ0).symm)

theorem rationalHermitianUnitaryPresentation_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    (rationalHermitianUnitaryPresentation E b hb hb0 δ hδ hδ0 g).val.val =
      g.val.val.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm :=
  rationalUnitaryPresentation_matrix E b hb δ hδ hδ0 g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation.Quadratic
