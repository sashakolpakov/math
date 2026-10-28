import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockProjection
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockTangent
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockOpenness

/-! # Prime Block Arithmetic Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockArithmeticOpenness

noncomputable section

/-! Arithmetic closure is open in a finite residue-prime block, assuming
the invariant quotient probabilities and full tangent space of the rational
commensurator. The tangent input is discharged in `RationalPrimeBlockTangents`. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}
  [Fintype ι] [Nonempty ι]

theorem primeBlock_arithmetic_tangentSpan_eq
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S U : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ U)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ i, CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    let W := fun J : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) =>
      Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
          (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (J.topologicalClosure : Set _)) 1)
    let T := Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1)
    W (Product.diagonalFiniteProduct G v).range = T → W (Product.arithmeticProductSubgroup G U v) = T := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  intro W T hR
  let H := Product.arithmeticProductSubgroup G U v
  let R := (Product.diagonalFiniteProduct G v).range
  have hcomm : ∀ g ∈ R, (H.map (MulAut.conj g).toMonoidHom).Commensurable H := by
    rintro g ⟨r, rfl⟩
    exact Product.arithmeticProduct_conjugate_commensurable G U v harch r
  apply PrimeBlockTangent.primeBlock_tangentSpan_eq_of_nonzero_projections
    G hconn hsimple hsemi v₀ v hv H R hcomm hR
  intro i
  exact PrimeBlockProjection.primeBlock_arithmetic_tangent_projection_nonzero
    G S U v₀ v hv hinj haway hSU hU hnoncompact i (hvolume i)

theorem primeBlock_arithmetic_closure_isOpen
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S U : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ U)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ i, CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (PrimeBlockDecomposition.finiteMatrixProductHom G v '' ((Product.diagonalFiniteProduct G v).range.topologicalClosure : Set _)) 1) =
      Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
          (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) →
    IsOpen ((Product.arithmeticProductSubgroup G U v).topologicalClosure :
      Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  intro hR
  have ht := primeBlock_arithmetic_tangentSpan_eq G hconn hsimple hsemi S U harch
    v₀ v hv hinj haway hSU hU hnoncompact hvolume hR
  exact PrimeBlockOpenness.primeBlock_isOpen_of_tangentSpan_le G v₀ v hv
    (Product.arithmeticProductSubgroup G U v).topologicalClosure
    (Product.arithmeticProductSubgroup G U v).isClosed_topologicalClosure ht.ge

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockArithmeticOpenness
