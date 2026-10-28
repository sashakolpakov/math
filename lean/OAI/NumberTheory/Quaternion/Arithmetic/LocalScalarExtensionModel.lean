import OAI.NumberTheory.Quaternion.Arithmetic.NormedAlgebraModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Local Scalar Extension Model -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarExtensionModel

noncomputable section

section

/-! A finite coefficient-field extension can be evaluated in a
complete local algebra by scalar extension and a faithful matrix model.
No choice of a prolongation of the local absolute value is needed. -/

open scoped Classical TensorProduct _root_.Matrix.Norms.Operator
open _root_.Topology

variable (F K E : Type*) [Field F] [NontriviallyNormedField K] [Algebra F K]
  [Field E] [Algebra F E] [FiniteDimensional F E]

abbrev scalarExtensionModel := NormedAlgebraModel.regularAlgebraModel K (K ⊗[F] E)

instance scalarExtensionModelAlgebra : Algebra F (scalarExtensionModel F K E) :=
  Algebra.compHom (scalarExtensionModel F K E) (algebraMap F K)

instance scalarExtensionModelTower : IsScalarTower F K (scalarExtensionModel F K E) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance scalarExtensionModelNontrivial : Nontrivial (scalarExtensionModel F K E) :=
  (NormedAlgebraModel.regularAlgebraModelEquiv K (K ⊗[F] E)).injective.nontrivial

def scalarExtensionCoefficients : E →ₐ[F] scalarExtensionModel F K E :=
  ((NormedAlgebraModel.regularAlgebraModelEquiv K (K ⊗[F] E)).toAlgHom.restrictScalars F).comp
    Algebra.TensorProduct.includeRight

theorem scalarExtensionCoefficients_algebraMap (a : F) :
    scalarExtensionCoefficients F K E (algebraMap F E a) =
      algebraMap K (scalarExtensionModel F K E) (algebraMap F K a) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F K (scalarExtensionModel F K E)]

def scalarExtensionMatrixEmbedding (n : ℕ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) (scalarExtensionModel F K E) :=
  (Algebra.ofId K (scalarExtensionModel F K E)).mapMatrix

theorem scalarExtensionMatrixEmbedding_injective (n : ℕ) :
    Function.Injective (scalarExtensionMatrixEmbedding F K E n) :=
  Matrix.map_injective (algebraMap K (scalarExtensionModel F K E)).injective

theorem scalarExtensionMatrixEmbedding_isClosedEmbedding [CompleteSpace K] (n : ℕ) :
    IsClosedEmbedding (scalarExtensionMatrixEmbedding F K E n) := by
  let : IsTopologicalAddGroup (scalarExtensionModel F K E) := inferInstance
  let : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (scalarExtensionModel F K E)) := by
    change IsTopologicalAddGroup (Fin n → Fin n → scalarExtensionModel F K E)
    infer_instance
  exact LinearMap.isClosedEmbedding_of_injective
    (f := (scalarExtensionMatrixEmbedding F K E n).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (scalarExtensionMatrixEmbedding_injective F K E n))

end

/-! The local scalar-extension model also carries the common scalar
field's continuous action, with no norm compatibility assumption. -/

open scoped Classical TensorProduct _root_.Matrix.Norms.Operator
open _root_.Topology

variable (F κ K E : Type*) [Field F] [Field κ] [NontriviallyNormedField K]
  [Algebra F K] [Algebra κ K] [Field E] [Algebra F E] [FiniteDimensional F E]

abbrev scalarExtensionModelScalarAlgebra : Algebra κ (scalarExtensionModel F K E) :=
  Algebra.compHom (scalarExtensionModel F K E) (algebraMap κ K)

theorem scalarExtensionModelScalarTower :
    letI := scalarExtensionModelScalarAlgebra F κ K E
    IsScalarTower κ K (scalarExtensionModel F K E) := by
  let := scalarExtensionModelScalarAlgebra F κ K E
  exact IsScalarTower.of_algebraMap_eq' rfl

theorem scalarExtensionModelScalarFinite [FiniteDimensional κ K] :
    letI := scalarExtensionModelScalarAlgebra F κ K E
    FiniteDimensional κ (scalarExtensionModel F K E) := by
  let := scalarExtensionModelScalarAlgebra F κ K E
  let := scalarExtensionModelScalarTower F κ K E
  exact Module.Finite.trans K (scalarExtensionModel F K E)

theorem scalarExtensionModelScalarContinuous [TopologicalSpace κ] [ContinuousSMul κ K] :
    letI := scalarExtensionModelScalarAlgebra F κ K E
    ContinuousSMul κ (scalarExtensionModel F K E) := by
  let := scalarExtensionModelScalarAlgebra F κ K E
  let := scalarExtensionModelScalarTower F κ K E
  exact IsScalarTower.continuousSMul K

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarExtensionModel
