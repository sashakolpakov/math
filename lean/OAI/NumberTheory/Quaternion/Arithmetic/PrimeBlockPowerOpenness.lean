import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockOpenness
import OAI.NumberTheory.Quaternion.Arithmetic.TangentPowers

/-! # Prime Block Power Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockPowerOpenness

noncomputable section

/-! Containing one fixed positive power of every sufficiently small
element makes a closed subgroup of a residue-prime block open. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem primeBlock_isOpen_of_eventually_pow_mem
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v₀ : HeightOneSpectrum (𝓞 F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))))
    (N : ℕ) (hN : 0 < N)
    (hpow : ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))), g ^ N ∈ H) :
    IsOpen (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  let : CharZero (v₀.adicCompletion F) := Algebra.charZero_of_charZero F (v₀.adicCompletion F)
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  have he : IsClosedEmbedding (PrimeBlockDecomposition.finiteMatrixProductHom G v) :=
    IsClosedEmbedding.piMap (fun i => IntegralCompact.localPoints_closedEmbedding G _)
  apply PrimeBlockOpenness.primeBlock_isOpen_of_tangentSpan_le G v₀ v hv H hH
  exact TangentPowers.tangentSpan_le_of_eventually_group_pow_mem (κ := κ)
    (PrimeBlockDecomposition.finiteMatrixProductHom G v) he.isEmbedding H N hN hpow

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockPowerOpenness
