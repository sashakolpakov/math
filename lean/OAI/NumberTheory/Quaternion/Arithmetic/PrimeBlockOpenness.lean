import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockAlgebraEmbedding
import OAI.NumberTheory.Quaternion.Arithmetic.RepresentedGroupOpenness
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition

/-! # Prime Block Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockOpenness

noncomputable section

/-! Equality of intrinsic tangent spans implies openness of a closed
subgroup of a finite residue-prime block of local point groups. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem primeBlock_isOpen_of_tangentSpan_le
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v₀ : HeightOneSpectrum (𝓞 F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) ≤
    Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) →
          IsOpen (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  let : ∀ i, FiniteDimensional κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_finiteDimensional v₀ (v i) (hv i)
  let : ∀ i, ContinuousSMul κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_continuousSMul v₀ (v i) (hv i)
  intro hspan
  obtain ⟨d, f, hf⟩ := PrimeBlockAlgebraEmbedding.exists_primeBlock_algebra_embedding (n := n) v₀ v hv
  have he : IsClosedEmbedding (PrimeBlockDecomposition.finiteMatrixProductHom G v) :=
    IsClosedEmbedding.piMap (fun i => IntegralCompact.localPoints_closedEmbedding G _)
  exact RepresentedGroupOpenness.matrix_represented_group_isOpen_of_tangentSpan_le v₀ f hf
    (PrimeBlockDecomposition.finiteMatrixProductHom G v) he H hH hspan

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockOpenness
