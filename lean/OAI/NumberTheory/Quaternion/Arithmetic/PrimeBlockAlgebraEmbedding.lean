import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding

/-! # Prime Block Algebra Embedding -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockAlgebraEmbedding

noncomputable section

/-! A finite residue-prime block admits a closed faithful algebra
representation over a chosen completion with that residue characteristic. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem exists_primeBlock_algebra_embedding
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i)) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    ∃ d : ℕ, ∃ f : (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) →ₐ[
      TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)] Matrix (Fin d) (Fin d) (v₀.adicCompletion F),
      IsClosedEmbedding f := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  let : ∀ i, FiniteDimensional κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_finiteDimensional v₀ (v i) (hv i)
  let : ∀ i, ContinuousSMul κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_continuousSMul v₀ (v i) (hv i)
  let A := ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)
  exact ⟨Module.finrank κ A, RegularMatrixEmbedding.regularMatrixEmbedding (κ := κ) (K := v₀.adicCompletion F) (A := A),
    RegularMatrixEmbedding.regularMatrixEmbedding_isClosedEmbedding⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockAlgebraEmbedding
