import OAI.NumberTheory.Quaternion.Arithmetic.BlockAssembly
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockArithmeticOpenness

/-! # Finite Product Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductOpenness

noncomputable section

/-! Openness of simultaneous arithmetic closure at arbitrary finitely
many finite places. This criterion states quotient invariant probabilities
and rational prime-block tangent equalities as inputs; the latter are
proved in `RationalPrimeBlockTangents`. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

def RationalPrimeBlockTangentFull (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i)) : Prop :=
  letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
    (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (PrimeBlockDecomposition.finiteMatrixProductHom G v '' ((Product.diagonalFiniteProduct G v).range.topologicalClosure : Set _)) 1) =
    Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1)

theorem arithmetic_finite_product_closure_isOpen
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S U : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (v : ι → HeightOneSpectrum (𝓞 F))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ i, CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩}))
    (hR : ∀ i₀ : ι, RationalPrimeBlockTangentFull G (v i₀)
      (fun i : {i : ι // LocalCompletion.residuePrime (v i) = LocalCompletion.residuePrime (v i₀)} => v i.val)
      (fun i => i.property.symm)) :
    IsOpen ((Product.arithmeticProductSubgroup G U v).topologicalClosure :
      Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  apply BlockAssembly.arithmetic_closure_isOpen_of_primeBlock_closures G S U v hinj haway hSU hU
  intro q hq
  obtain ⟨i₀, _, rfl⟩ := Finset.mem_image.mp hq
  let p := fun i => LocalCompletion.residuePrime (v i) = LocalCompletion.residuePrime (v i₀)
  let : Nonempty {i : ι // p i} := ⟨⟨i₀, rfl⟩⟩
  let w := fun i : {i : ι // p i} => v i.val
  have hw : Function.Injective w := hinj.comp Subtype.val_injective
  have hwaway : ∀ i, Sum.inr (w i) ∉ S := fun i => haway i.val
  have hbS := BlockComplement.arithmeticBlockPlaces_contains_base S v p
  exact PrimeBlockArithmeticOpenness.primeBlock_arithmetic_closure_isOpen G hconn hsimple hsemi
    S (BlockComplement.arithmeticBlockPlaces S v p) (fun a => hbS (harch a))
    (v i₀) w (fun i => i.property.symm) hw hwaway hbS
    (BlockComplement.arithmeticBlockPlaces_contains_block S v p) hnoncompact (fun i => hvolume i.val) (hR i₀)

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductOpenness
