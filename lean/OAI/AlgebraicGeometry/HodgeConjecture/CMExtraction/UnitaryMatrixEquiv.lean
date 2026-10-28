import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Unitary Matrix Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic

noncomputable section

/-! Identify the actual determinant-one matrices preserving the native
sesquilinear form with the unitary matrices used by the adelic construction.
The identification leaves every matrix entry unchanged. -/

open scoped Classical

variable {R : Type*} [CommRing R] [StarRing R]

def diagonalForm (b : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal (Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b)

theorem unitary_matrix_iff (b : R) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL R) :
    g ∈ Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (starRingEnd R) b ↔
      g.val.conjTranspose * diagonalForm b * g.val = diagonalForm b := by
  rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitary_iff_columns]
  constructor
  · intro h
    ext i j
    change (∑ k, (g.val.conjTranspose * diagonalForm b) i k * g.val k j) = _
    simp only [diagonalForm, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    calc
      _ = ∑ k, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b k * g.val k j * star (g.val k i) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = if j = i then Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b j else 0 := h j i
      _ = (Matrix.diagonal (Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b)) i j := by
        by_cases hij : i = j
        · subst j; simp
        · simp [Matrix.diagonal, hij, Ne.symm hij]
  · intro h i j
    have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A j i) h
    change (∑ k, (g.val.conjTranspose * diagonalForm b) j k * g.val k i) = _ at hij
    simp only [diagonalForm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at hij
    calc
      _ = ∑ k, (star (g.val k j) * Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b k) * g.val k i := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [starRingEnd_apply]
        ring
      _ = (Matrix.diagonal (Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b)) j i := hij
      _ = if i = j then Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b i else 0 := by
        by_cases he : i = j
        · subst j; simp
        · simp [Matrix.diagonal, he, Ne.symm he]

def unitaryMatrixMap (b : R) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd R) b →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (diagonalForm b) where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g.val,
    (unitary_matrix_iff b g.val).mp g.property, by
      apply Units.ext
      exact g.val.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

theorem unitaryMatrixMap_bijective (b : R) : Function.Bijective (unitaryMatrixMap b) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val he
  · intro g
    have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
    let A : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL R := ⟨g.val.val, hd⟩
    refine ⟨⟨A, (unitary_matrix_iff b A).mpr g.property.1⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rfl

def unitaryMatrixEquiv (b : R) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd R) b ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (diagonalForm b) :=
  MulEquiv.ofBijective (unitaryMatrixMap b) (unitaryMatrixMap_bijective b)

theorem unitaryMatrixEquiv_matrix (b : R) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd R) b) :
    (unitaryMatrixEquiv b g).val.val = g.val.val := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryMatrixEquiv.Quadratic
