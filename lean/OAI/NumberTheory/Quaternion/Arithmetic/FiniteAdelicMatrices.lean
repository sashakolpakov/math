import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicPolynomialValues
import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm

/-! # Finite Adelic Matrices -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices

noncomputable section

/-! Actual finite-adelic group points give invertible matrices over
the finite adele ring, and hence the full lattices used in reduction. -/

open scoped Classical _root_.NumberField RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def scalarFiniteAdeleEvaluation (v : HeightOneSpectrum (𝓞 F)) :
    ScalarApproximation.ScalarFiniteAdeles F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v

abbrev FiniteAdelicGroupPoints (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [LocalAdeles.LocalPoints G (.inr v), LocalAdeles.integralLocalSubgroup G (.inr v)]

def finiteAdelicMatrix (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : FiniteAdelicGroupPoints G) :
    Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F) := fun i j =>
  ⟨fun v => (g v).val i j, by
    filter_upwards [g.property] with v hv
    exact hv.1 i j⟩

theorem finiteAdelicMatrix_eval (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : FiniteAdelicGroupPoints G)
    (v : HeightOneSpectrum (𝓞 F)) :
    (scalarFiniteAdeleEvaluation v).mapMatrix (finiteAdelicMatrix G g) =
      PolynomialGaloisNorm.matrixPointsHom G (LocalAdeles.localEmbedding (.inr v)) (g v) := rfl

theorem finiteAdele_matrix_ext {A B : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)}
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      (scalarFiniteAdeleEvaluation v).mapMatrix A = (scalarFiniteAdeleEvaluation v).mapMatrix B) : A = B := by
  apply Matrix.ext
  intro i j
  apply RestrictedProduct.ext
  intro v
  exact congrFun (congrFun (h v) i) j

def finiteAdelicMatrixHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    FiniteAdelicGroupPoints G →* Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F) where
  toFun := finiteAdelicMatrix G
  map_one' := by
    apply finiteAdele_matrix_ext
    intro v
    rw [finiteAdelicMatrix_eval, map_one]
    exact map_one (PolynomialGaloisNorm.matrixPointsHom G (LocalAdeles.localEmbedding (.inr v)))
  map_mul' g h := by
    apply finiteAdele_matrix_ext
    intro v
    rw [finiteAdelicMatrix_eval, map_mul, finiteAdelicMatrix_eval, finiteAdelicMatrix_eval]
    exact map_mul (PolynomialGaloisNorm.matrixPointsHom G (LocalAdeles.localEmbedding (.inr v))) (g v) (h v)

def finiteAdelicMatrixUnitHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    FiniteAdelicGroupPoints G →* (Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F))ˣ :=
  (finiteAdelicMatrixHom G).toHomUnits

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices
