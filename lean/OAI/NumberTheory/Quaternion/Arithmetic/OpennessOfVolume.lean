import OAI.NumberTheory.Quaternion.Arithmetic.RationalLocalTangent
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductOpenness
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteScalarDensity

/-! # Openness Of Volume -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OpennessOfVolume

noncomputable section

section

/-! The rational commensurator has the full tangent space in every
finite residue-prime block. This discharges the rational tangent input
of the arithmetic openness criterion. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open IsDedekindDomain Set _root_.Topology

attribute [local instance] LieRing.ofAssociativeRing

theorem rationalPrimeBlockTangentFull
    {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i)) (hinj : Function.Injective v) :
    FiniteProductOpenness.RationalPrimeBlockTangentFull G v₀ v hv := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  let : ∀ i, FiniteDimensional κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_finiteDimensional v₀ (v i) (hv i)
  let : ∀ i, ContinuousSMul κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_continuousSMul v₀ (v i) (hv i)
  change Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
    ((Product.diagonalFiniteProduct G v).range.topologicalClosure : Set _)) 1) =
      Submodule.span κ (tangentConeAt κ (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1)
  by_cases hi : IsEmpty ι
  · let := hi
    exact Subsingleton.elim _ _
  let : Nonempty ι := not_isEmpty_iff.mp hi
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    let C := PrimeBlockDecomposition.finiteMatrixProductHom G v '' ((Product.diagonalFiniteProduct G v).range.topologicalClosure : Set _)
    have hf : IsClosedEmbedding (PrimeBlockDecomposition.finiteMatrixProductHom G v) :=
      IsClosedEmbedding.piMap (fun i => IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v i)))
    have hC : IsClosed C := hf.isClosedMap _ (Product.diagonalFiniteProduct G v).range.isClosed_topologicalClosure
    have hrational : ∀ g : G.RationalPoints,
        (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map
          (algebraMap F ((v i).adicCompletion F))) ∈ C := by
      intro g
      exact ⟨Product.diagonalFiniteProduct G v g,
        (Product.diagonalFiniteProduct G v).range.le_topologicalClosure ⟨g, rfl⟩, rfl⟩
    apply le_antisymm
    · apply Submodule.span_mono
      apply tangentConeAt_mono
      rintro X ⟨g, _, rfl⟩
      exact ⟨g, rfl⟩
    · rw [PrimeBlockInfinitesimal.primeBlock_tangentSpan_eq_infinitesimal_product G hconn v₀ v hv]
      intro X hX
      apply RationalLocalTangent.rational_closure_tangentSpan_contains_local_infinitesimals (κ := κ)
        G hconn hsemi (FiniteScalarDensity.denseRange_finiteScalarDiagonal v hinj) C hC hrational X
      intro i
      exact hX i (mem_univ i)

end

/-! Openness of the finite-product arithmetic closure now requires
only the quotient invariant probabilities. The full rational tangent
input follows from the proved algebraic and weak approximation results. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

theorem arithmetic_finite_product_closure_isOpen_of_volume
    {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S U : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (v : ι → HeightOneSpectrum (𝓞 F))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ i, CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    IsOpen ((Product.arithmeticProductSubgroup G U v).topologicalClosure :
      Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  apply FiniteProductOpenness.arithmetic_finite_product_closure_isOpen G hconn hsimple hsemi S U harch
    v hinj haway hSU hU hnoncompact hvolume
  intro i₀
  exact rationalPrimeBlockTangentFull G hconn hsemi (v i₀) _ _
    (hinj.comp Subtype.val_injective)

end

end OAI.NumberTheory.Quaternion.Arithmetic.OpennessOfVolume
