import OAI.NumberTheory.Quaternion.Arithmetic.IntegralTraceTangentSpan
import OAI.NumberTheory.Quaternion.Arithmetic.ScalarExtensionProduct
import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding

/-! # Trace Tangents Descent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TraceTangentsDescent

noncomputable section

/-! The auxiliary scalar-extension algebras can be eliminated: trace
spanning gives tangent directions in the original local matrix spaces. -/

open scoped Classical _root_.Matrix.Norms.Operator
open Set _root_.Topology

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] {ι : Type*} [Fintype ι] [Nonempty ι]
  {κ : Type*} [NontriviallyNormedField κ] [CompleteSpace κ] {K : ι → Type*}
  [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
  [∀ i, CompleteSpace (K i)] [∀ i, FiniteDimensional κ (K i)] [∀ i, ContinuousSMul κ (K i)]
  {n : ℕ}

theorem trace_span_mem_original_tangentSpan (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F)
    (hspan : S ∈ Submodule.span F {Z | ∃ a : E, ∃ Y ∈ IntegralSemisimpleDirections.integralPolynomialDirections
      (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)) (S.map (algebraMap F E)),
        Z = GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • Y)})
    (b : ∀ i, K i)
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (K i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (K i))) ∈ C) :
    (fun i => b i • S.map (algebraMap F (K i))) ∈ Submodule.span κ (tangentConeAt κ C 1) := by
  let A : ι → Type _ := fun i => LocalScalarExtensionModel.scalarExtensionModel F (K i) E
  let : ∀ i, Algebra κ (A i) := fun i => LocalScalarExtensionModel.scalarExtensionModelScalarAlgebra F κ (K i) E
  let : ∀ i, IsScalarTower κ (K i) (A i) := fun i => LocalScalarExtensionModel.scalarExtensionModelScalarTower F κ (K i) E
  let : ∀ i, FiniteDimensional κ (A i) := fun i => LocalScalarExtensionModel.scalarExtensionModelScalarFinite F κ (K i) E
  let : ∀ i, ContinuousSMul κ (A i) := fun i => LocalScalarExtensionModel.scalarExtensionModelScalarContinuous F κ (K i) E
  let : ∀ i, IsTopologicalAddGroup (A i) := fun _ => inferInstance
  let : ∀ i, IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (A i)) := by
    intro i
    change IsTopologicalAddGroup (Fin n → Fin n → A i)
    infer_instance
  let e := ScalarExtensionProduct.scalarExtensionProductEmbedding F κ E K n
  have he : IsClosedEmbedding e := ScalarExtensionProduct.scalarExtensionProductEmbedding_isClosedEmbedding F κ E K n
  let D := e '' C
  have hD : IsClosed D := he.isClosedMap C hC
  have hrat : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i))) ∈ D := by
    intro g
    refine ⟨_, hrational g, ?_⟩
    simpa only [one_smul] using
      ScalarExtensionProduct.scalarExtensionProductEmbedding_scaled F κ E K (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g)
        (fun i => (1 : K i))
  have hs := IntegralTraceTangentSpan.integral_trace_span_local_multiples_mem_tangentSpan (K := K) (A := A)
    G S hspan (fun i => LocalScalarExtensionModel.scalarExtensionCoefficients F (K i) E) b
    (fun i => continuous_algebraMap κ (K i)) hdense D hD hrat
  apply (RegularMatrixEmbedding.algebraHom_tangentSpan_image_mem_iff e he C _).mp
  have hx := ScalarExtensionProduct.scalarExtensionProductEmbedding_scaled F κ E K S b
  exact hx.symm ▸ hs

end

end OAI.NumberTheory.Quaternion.Arithmetic.TraceTangentsDescent
