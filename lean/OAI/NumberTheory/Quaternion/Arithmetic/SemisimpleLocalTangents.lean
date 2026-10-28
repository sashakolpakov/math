import OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleTraceSpan
import OAI.NumberTheory.Quaternion.Arithmetic.TraceTangentsDescent

/-! # Semisimple Local Tangents -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleLocalTangents

noncomputable section

/-! Semisimple global Lie elements, with arbitrary independent local
scalar multiples, are tangent directions of the rational-point closure. -/

open scoped Classical _root_.Matrix.Norms.Operator
open Set

theorem semisimple_local_multiples_mem_tangentSpan
    {F : Type} [Field F] [CharZero F] {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : Type*} [NontriviallyNormedField κ] [CompleteSpace κ] {K : ι → Type*}
    [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
    [∀ i, CompleteSpace (K i)] [∀ i, FiniteDimensional κ (K i)] [∀ i, ContinuousSMul κ (K i)]
    {n : ℕ} [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected)
    (S : Matrix (Fin n) (Fin n) F) (hLie : S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) (b : ∀ i, K i)
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (K i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (K i))) ∈ C) :
    (fun i => b i • S.map (algebraMap F (K i))) ∈ Submodule.span κ (tangentConeAt κ C 1) := by
  obtain ⟨L, hL⟩ := SemisimpleTraceSpan.semisimple_mem_span_finiteGalois_traces G hG S hLie hS
  exact TraceTangentsDescent.trace_span_mem_original_tangentSpan (E := L) G S hL b hdense C hC hrational

end

end OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleLocalTangents
