import OAI.NumberTheory.Quaternion.Arithmetic.Product
import OAI.NumberTheory.Quaternion.Arithmetic.IntrinsicProjection
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockAlgebraEmbedding

/-! # Prime Block Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockProjection

noncomputable section

/-! Single-place arithmetic nondiscreteness supplies a nonzero tangent
projection in every factor of a finite residue-prime block. The faithful
matrix representation is eliminated from the conclusion. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem primeBlock_arithmetic_tangent_projection_nonzero
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S U : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (i : ι) (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    letI : ∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F) :=
      fun j => PrimeField.primeBlockScalarAlgebra v₀ (v j) (hv j)
    ∃ a ∈ Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
          ((Product.arithmeticProductSubgroup G U v).topologicalClosure : Set _)) 1), a i ≠ 0 := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : ∀ j, Algebra κ ((v j).adicCompletion F) := fun j => PrimeField.primeBlockScalarAlgebra v₀ (v j) (hv j)
  let : ∀ j, FiniteDimensional κ ((v j).adicCompletion F) :=
    fun j => PrimeField.primeBlockScalar_finiteDimensional v₀ (v j) (hv j)
  let : ∀ j, ContinuousSMul κ ((v j).adicCompletion F) :=
    fun j => PrimeField.primeBlockScalar_continuousSMul v₀ (v j) (hv j)
  obtain ⟨d, f, hf⟩ := PrimeBlockAlgebraEmbedding.exists_primeBlock_algebra_embedding (n := n) v₀ v hv
  let H := Product.arithmeticProductSubgroup G U v
  exact IntrinsicProjection.matrix_arithmetic_product_intrinsic_projection_nonzero
    G S v₀ v hinj haway i f hf H.topologicalClosure H.isClosed_topologicalClosure
    (fun g => H.le_topologicalClosure (Product.singlePlaceArithmetic_mem_product G S U v hSU i (hU i) g))
    hnoncompact hvolume

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockProjection
