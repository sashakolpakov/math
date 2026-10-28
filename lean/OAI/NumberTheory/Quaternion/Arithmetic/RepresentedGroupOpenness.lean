import OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedGroupOpenness
import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarRestriction

/-! # Represented Group Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RepresentedGroupOpenness

noncomputable section

/-! The local openness criterion can be applied before choosing a
faithful matrix representation of a finite-dimensional topological algebra. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

section

variable {F : Type} [Field F] [NumberField F]

theorem represented_group_isOpen_of_tangentSpan_le (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [ContinuousSMul (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    {D : Type*} [NormedRing D] [NormedAlgebra (v.adicCompletion F) D] [CompleteSpace D]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) D]
    (f : A →ₐ[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] D) (hf : IsClosedEmbedding f)
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (e : L →* A) (he : IsClosedEmbedding e) (H : Subgroup L) (hH : IsClosed (H : Set L))
    (hspan : Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (range e) 1) ≤
        Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
          (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (e '' (H : Set L)) 1)) :
    IsOpen (H : Set L) := by
  let κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  let : NormedAlgebra κ D := OrderedProductDerivative.finitePrimeNormedAlgebra v D
  apply EmbeddedGroupOpenness.embedded_group_isOpen_of_tangentSpan_le v (f.toMonoidHom.comp e) (hf.comp he) H hH
  rw [← Submonoid.map_map, ← Submonoid.map_map]
  change Submodule.span κ (tangentConeAt κ (f '' (e '' (univ : Set L))) 1) ≤
    Submodule.span κ (tangentConeAt κ (f '' (e '' (H : Set L))) 1)
  rw [image_univ, RegularMatrixEmbedding.algebraHom_tangentSpan_image f hf, RegularMatrixEmbedding.algebraHom_tangentSpan_image f hf]
  exact Submodule.map_mono hspan

end

open scoped _root_.Matrix.Norms.Operator

variable {F : Type} [Field F] [NumberField F]

theorem matrix_represented_group_isOpen_of_tangentSpan_le (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [ContinuousSMul (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    {d : ℕ}
    (f : A →ₐ[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      Matrix (Fin d) (Fin d) (v.adicCompletion F)) (hf : IsClosedEmbedding f)
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (e : L →* A) (he : IsClosedEmbedding e) (H : Subgroup L) (hH : IsClosed (H : Set L))
    (hspan : Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (range e) 1) ≤
        Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
          (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (e '' (H : Set L)) 1)) :
    IsOpen (H : Set L) := by
  let : FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) :=
    LocalCompletion.finiteCompletion_finiteDimensional_closedPrime v
  let D := Matrix (Fin d) (Fin d) (v.adicCompletion F)
  let : @CompleteSpace D (inferInstance : NormedRing D).toUniformSpace :=
    FiniteDimensional.complete (v.adicCompletion F) D
  exact represented_group_isOpen_of_tangentSpan_le (A := A) (D := D) v
    (MatrixScalarRestriction.matrixAlgHom_primeRestriction (K := v.adicCompletion F) (A := A) (d := d) f)
    (MatrixScalarRestriction.matrixAlgHom_primeRestriction_isClosedEmbedding (K := v.adicCompletion F) f hf)
    e he H hH hspan

end

end OAI.NumberTheory.Quaternion.Arithmetic.RepresentedGroupOpenness
