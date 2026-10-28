import OAI.NumberTheory.Quaternion.Arithmetic.NormTraceTangents
import OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarSpan
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralSemisimpleDirections

/-! # Integral Trace Tangent Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralTraceTangentSpan

noncomputable section

/-! The algebraic trace span is contained in the analytic tangent
span, including independent scalar multiples at each selected place. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix Set

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] {ι : Type*} [Fintype ι] [Nonempty ι]
  {κ : Type*} [NontriviallyNormedField κ] {K A : ι → Type*}
  [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
  [∀ i, NormedCommRing (A i)] [∀ i, Nontrivial (A i)] [∀ i, Algebra F (A i)]
  [∀ i, Algebra κ (A i)] [∀ i, NormedAlgebra (K i) (A i)]
  [∀ i, IsScalarTower F (K i) (A i)] [∀ i, IsScalarTower κ (K i) (A i)]
  [∀ i, CompleteSpace (K i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional (K i) (A i)]
  {n : ℕ}

theorem integral_trace_span_local_multiples_mem_tangentSpan (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F)
    (hspan : S ∈ Submodule.span F {Z | ∃ a : E, ∃ Y ∈ IntegralSemisimpleDirections.integralPolynomialDirections
      (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)) (S.map (algebraMap F E)),
        Z = GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • Y)})
    (f : ∀ i, E →ₐ[F] A i) (b : ∀ i, K i)
    (he : ∀ i, Continuous (algebraMap κ (K i)))
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (A i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i))) ∈ C) :
    LocalScalarSpan.locallyScaledMatrix (A := A) S b ∈ Submodule.span κ (tangentConeAt κ C 1) := by
  apply LocalScalarSpan.locallyScaledMatrix_mem_of_span (Submodule.span κ (tangentConeAt κ C 1)) _ ?_ hspan b
  rintro Z ⟨a, Y, hY, rfl⟩ c
  obtain ⟨B, m, rfl, hLie, hpoly⟩ := hY
  exact Submodule.subset_span (NormTraceTangents.norm_trace_local_multiples_mem_tangentCone
    G S B m hLie hpoly f a c he hdense C hC hrational)

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralTraceTangentSpan
