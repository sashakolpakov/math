import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding

/-! # Normed Algebra Model -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NormedAlgebraModel

noncomputable section

/-! Every finite-dimensional commutative algebra over a complete
nontrivially normed field has a concrete complete normed matrix model.
This permits local evaluation after scalar extension without requiring
the scalar-extension algebra to be a field. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable (K C : Type*) [NontriviallyNormedField K] [CommRing C] [Algebra K C]
  [FiniteDimensional K C]

abbrev regularAlgebraModel :=
  (RegularMatrixEmbedding.regularMatrixEmbedding (κ := K) (K := K) (A := C)).range

def regularAlgebraModelEquiv : C ≃ₐ[K] regularAlgebraModel K C :=
  AlgEquiv.ofInjective (RegularMatrixEmbedding.regularMatrixEmbedding (κ := K) (K := K) (A := C))
    RegularMatrixEmbedding.regularMatrixEmbedding_injective

instance regularAlgebraModelNormedCommRing : NormedCommRing (regularAlgebraModel K C) :=
  { (inferInstance : NormedRing (regularAlgebraModel K C)) with
    mul_comm := fun a b => (regularAlgebraModelEquiv K C).symm.injective (by
      rw [map_mul, map_mul, mul_comm]) }

instance regularAlgebraModelTopology : TopologicalSpace (regularAlgebraModel K C) :=
  (regularAlgebraModelNormedCommRing K C).toUniformSpace.toTopologicalSpace

instance regularAlgebraModelUniformity : UniformSpace (regularAlgebraModel K C) :=
  (regularAlgebraModelNormedCommRing K C).toUniformSpace

instance regularAlgebraModelNormedAlgebra : NormedAlgebra K (regularAlgebraModel K C) :=
  Subalgebra.toNormedAlgebra _

instance regularAlgebraModelFinite : FiniteDimensional K (regularAlgebraModel K C) :=
  Module.Finite.of_surjective (regularAlgebraModelEquiv K C).toLinearMap
    (regularAlgebraModelEquiv K C).surjective

instance regularAlgebraModelComplete [CompleteSpace K] :
    @CompleteSpace (regularAlgebraModel K C)
      (inferInstance : NormedRing (regularAlgebraModel K C)).toUniformSpace :=
  FiniteDimensional.complete K _

end

end OAI.NumberTheory.Quaternion.Arithmetic.NormedAlgebraModel
