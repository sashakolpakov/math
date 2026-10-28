import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Noncommutative Local Model -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NoncommutativeLocalModel

noncomputable section

/-! Concrete complete normed models of local scalar extensions of
finite-dimensional algebras, including noncommutative algebras. -/

open scoped Classical TensorProduct _root_.Matrix.Norms.Operator

variable (K A : Type*) [NontriviallyNormedField K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

abbrev finiteAlgebraNormedModel :=
  (RegularMatrixEmbedding.regularMatrixEmbedding (κ := K) (K := K) (A := A)).range

def finiteAlgebraNormedModelEquiv : A ≃ₐ[K] finiteAlgebraNormedModel K A :=
  AlgEquiv.ofInjective (RegularMatrixEmbedding.regularMatrixEmbedding (κ := K) (K := K) (A := A))
    RegularMatrixEmbedding.regularMatrixEmbedding_injective

instance finiteAlgebraNormedModelNormedRing : NormedRing (finiteAlgebraNormedModel K A) :=
  inferInstance

instance finiteAlgebraNormedModelTopology : TopologicalSpace (finiteAlgebraNormedModel K A) :=
  (inferInstance : NormedRing (finiteAlgebraNormedModel K A)).toUniformSpace.toTopologicalSpace

instance finiteAlgebraNormedModelUniformity : UniformSpace (finiteAlgebraNormedModel K A) :=
  (inferInstance : NormedRing (finiteAlgebraNormedModel K A)).toUniformSpace

instance finiteAlgebraNormedModelNormedAlgebra : NormedAlgebra K (finiteAlgebraNormedModel K A) :=
  Subalgebra.toNormedAlgebra _

instance finiteAlgebraNormedModelFinite : FiniteDimensional K (finiteAlgebraNormedModel K A) :=
  Module.Finite.of_surjective (finiteAlgebraNormedModelEquiv K A).toLinearMap
    (finiteAlgebraNormedModelEquiv K A).surjective

instance finiteAlgebraNormedModelComplete [CompleteSpace K] :
    @CompleteSpace (finiteAlgebraNormedModel K A)
      (inferInstance : NormedRing (finiteAlgebraNormedModel K A)).toUniformSpace :=
  FiniteDimensional.complete K _

instance finiteAlgebraNormedModelOpenUnits [CompleteSpace K] :
    IsOpenUnits (finiteAlgebraNormedModel K A) := ⟨Units.isOpenEmbedding_val⟩

variable (F : Type*) [Field F] [Algebra F K]
  (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D]

abbrev localFiniteAlgebra := finiteAlgebraNormedModel K (K ⊗[F] D)

instance localFiniteAlgebraBaseAlgebra : Algebra F (localFiniteAlgebra K F D) :=
  Algebra.compHom (localFiniteAlgebra K F D) (algebraMap F K)

instance localFiniteAlgebraTower : IsScalarTower F K (localFiniteAlgebra K F D) :=
  IsScalarTower.of_algebraMap_eq' rfl

def localFiniteAlgebraCoefficients : D →ₐ[F] localFiniteAlgebra K F D :=
  ((finiteAlgebraNormedModelEquiv K (K ⊗[F] D)).toAlgHom.restrictScalars F).comp
    Algebra.TensorProduct.includeRight

theorem localFiniteAlgebraCoefficients_injective :
    Function.Injective (localFiniteAlgebraCoefficients K F D) :=
  (finiteAlgebraNormedModelEquiv K (K ⊗[F] D)).injective.comp
    (Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective)

def localFiniteAlgebraBasis {ι : Type*} (b : Module.Basis ι F D) :
    Module.Basis ι K (localFiniteAlgebra K F D) :=
  (b.baseChange K).map (finiteAlgebraNormedModelEquiv K (K ⊗[F] D)).toLinearEquiv

theorem localFiniteAlgebraBasis_apply {ι : Type*} (b : Module.Basis ι F D) (i : ι) :
    localFiniteAlgebraBasis K F D b i = localFiniteAlgebraCoefficients K F D (b i) := by
  simp only [localFiniteAlgebraBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.NoncommutativeLocalModel
