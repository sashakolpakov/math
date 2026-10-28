import OAI.NumberTheory.Quaternion.Arithmetic.IntegralBlockComplement
import OAI.NumberTheory.Quaternion.Arithmetic.CompactBlockPowers
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockPowerOpenness

/-! # Prime Block Compact Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockCompactProjection

noncomputable section

/-! If arithmetic points have an open closure in one residue-prime
block and integral complementary coordinates, the subgroup supported
on that block is open inside the block. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem primeBlock_comap_isOpen_of_open_compact_projection
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : LocalCompletion.residuePrime v₀ = q)
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))))
    (Γ : Subgroup (IntegralBlockComplement.integralBlockComplement G v (fun i => LocalCompletion.residuePrime (v i) = q) ×
      IntegralBlockComplement.localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q)))
    (hΓ : ∀ g ∈ Γ, IntegralBlockComplement.insertIntegralBlockComplement G v _ g ∈ H)
    (hP : IsOpen ((Γ.map (MonoidHom.snd _ _)).topologicalClosure :
      Set (IntegralBlockComplement.localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q)))) :
    IsOpen (H.comap (IntegralBlockComplement.insertLocalBlock G v (fun i => LocalCompletion.residuePrime (v i) = q)) :
      Set (IntegralBlockComplement.localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q))) := by
  let p := fun i => LocalCompletion.residuePrime (v i) = q
  let e := IntegralBlockComplement.insertIntegralBlockComplement G v p
  let j := IntegralBlockComplement.insertLocalBlock G v p
  have hnear : ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))),
      g ∈ H → PrimeBlockDecomposition.localPrimeBlock G v q g ∈ H := by
    filter_upwards [PrimeBlockDecomposition.localPrimeBlock_eventually_mem G v H hH] with g hg hgm
    exact hg hgm q
  obtain ⟨N, hN, hpow⟩ := CompactBlockPowers.compact_factor_eventually_power_mem_of_open_projection
    e (IntegralBlockComplement.insertIntegralBlockComplement_continuous G v p)
    j (IntegralBlockComplement.insertLocalBlock_continuous G v p) (PrimeBlockDecomposition.localPrimeBlock G v q)
    (IntegralBlockComplement.localPrimeBlock_insertIntegralBlockComplement G v q) H hH hnear Γ hΓ hP
  exact PrimeBlockPowerOpenness.primeBlock_isOpen_of_eventually_pow_mem G v₀ (fun i : {i : ι // p i} => v i.val)
    (fun i => hq.trans i.property.symm) (H.comap j)
    (hH.preimage (IntegralBlockComplement.insertLocalBlock_continuous G v p)) N hN hpow

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockCompactProjection
