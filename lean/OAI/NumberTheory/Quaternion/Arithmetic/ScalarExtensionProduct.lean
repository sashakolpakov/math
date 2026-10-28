import OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarExtensionModel
import Mathlib.Algebra.Algebra.Pi

/-! # Scalar Extension Product -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ScalarExtensionProduct

noncomputable section

/-! Closed scalar-extension embeddings for a product of local matrix
algebras, viewed over their common scalar field. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Topology

variable (F κ E : Type*) [Field F] [Field κ] [Field E] [Algebra F E] [FiniteDimensional F E]
  {ι : Type*} (K : ι → Type*) [∀ i, NontriviallyNormedField (K i)]
  [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]

def scalarExtensionProductEmbedding (n : ℕ) :
    letI : ∀ i, Algebra κ (LocalScalarExtensionModel.scalarExtensionModel F (K i) E) :=
      fun i => LocalScalarExtensionModel.scalarExtensionModelScalarAlgebra F κ (K i) E
    (∀ i, Matrix (Fin n) (Fin n) (K i)) →ₐ[κ]
      (∀ i, Matrix (Fin n) (Fin n) (LocalScalarExtensionModel.scalarExtensionModel F (K i) E)) := by
  let : ∀ i, Algebra κ (LocalScalarExtensionModel.scalarExtensionModel F (K i) E) :=
    fun i => LocalScalarExtensionModel.scalarExtensionModelScalarAlgebra F κ (K i) E
  let : ∀ i, IsScalarTower κ (K i) (LocalScalarExtensionModel.scalarExtensionModel F (K i) E) :=
    fun i => LocalScalarExtensionModel.scalarExtensionModelScalarTower F κ (K i) E
  exact AlgHom.pi (fun i => ((LocalScalarExtensionModel.scalarExtensionMatrixEmbedding F (K i) E n).restrictScalars κ).comp
    (Pi.evalAlgHom κ (fun i => Matrix (Fin n) (Fin n) (K i)) i))

theorem scalarExtensionProductEmbedding_isClosedEmbedding [∀ i, CompleteSpace (K i)] (n : ℕ) :
    IsClosedEmbedding (scalarExtensionProductEmbedding F κ E K n) := by
  exact IsClosedEmbedding.piMap (fun i => LocalScalarExtensionModel.scalarExtensionMatrixEmbedding_isClosedEmbedding F (K i) E n)

theorem scalarExtensionProductEmbedding_scaled {n : ℕ} (S : Matrix (Fin n) (Fin n) F)
    (b : ∀ i, K i) :
    scalarExtensionProductEmbedding F κ E K n
      (fun i => b i • S.map (algebraMap F (K i))) =
        fun i => b i • S.map (algebraMap F (LocalScalarExtensionModel.scalarExtensionModel F (K i) E)) := by
  funext i
  apply Matrix.ext
  intro j k
  change algebraMap (K i) (LocalScalarExtensionModel.scalarExtensionModel F (K i) E)
      (b i * algebraMap F (K i) (S j k)) =
    b i • algebraMap F (LocalScalarExtensionModel.scalarExtensionModel F (K i) E) (S j k)
  rw [map_mul, IsScalarTower.algebraMap_apply F (K i) (LocalScalarExtensionModel.scalarExtensionModel F (K i) E)]
  exact (Algebra.smul_def _ _).symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.ScalarExtensionProduct
