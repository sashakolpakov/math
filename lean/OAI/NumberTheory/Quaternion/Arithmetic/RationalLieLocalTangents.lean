import OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalSemisimpleSpan
import OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleLocalTangents

/-! # Rational Lie Local Tangents -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RationalLieLocalTangents

noncomputable section

/-! Every rational infinitesimal direction, with independent local
scalar multiples, belongs to the tangent span of the rational closure. -/

open scoped Classical _root_.Matrix.Norms.Operator
open Set

theorem rational_infinitesimal_local_multiples_mem_tangentSpan
    {F : Type} [Field F] [CharZero F] {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : Type*} [NontriviallyNormedField κ] [CompleteSpace κ] {K : ι → Type*}
    [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
    [∀ i, CompleteSpace (K i)] [∀ i, FiniteDimensional κ (K i)] [∀ i, ContinuousSMul κ (K i)]
    {n : ℕ} [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (X : Matrix (Fin n) (Fin n) F) (hLie : X ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) (b : ∀ i, K i)
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (K i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (K i))) ∈ C) :
    (fun i => b i • X.map (algebraMap F (K i))) ∈ Submodule.span κ (tangentConeAt κ C 1) := by
  have hX : X ∈ Submodule.span F (InfinitesimalSemisimpleSpan.semisimpleInfinitesimalMatrices G) :=
    InfinitesimalSemisimpleSpan.infinitesimalStabilizer_eq_span_semisimple G hG hsemi ▸ hLie
  apply LocalScalarSpan.locallyScaledMatrix_mem_of_span (A := K)
    (Submodule.span κ (tangentConeAt κ C 1)) _ ?_ hX b
  intro S hS c
  exact SemisimpleLocalTangents.semisimple_local_multiples_mem_tangentSpan G hG S hS.1 hS.2 c hdense C hC hrational

end

end OAI.NumberTheory.Quaternion.Arithmetic.RationalLieLocalTangents
