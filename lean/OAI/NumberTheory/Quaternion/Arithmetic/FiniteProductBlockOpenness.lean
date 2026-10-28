import OAI.NumberTheory.Quaternion.Arithmetic.IntegralBlockComplement
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition

/-! # Finite Product Block Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductBlockOpenness

noncomputable section

/-! Open supported subgroups in all occurring residue-prime blocks
give an open subgroup of the entire finite local product. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem local_product_isOpen_of_block_comaps
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hblock : ∀ q ∈ Finset.univ.image (fun i => LocalCompletion.residuePrime (v i)),
      IsOpen (H.comap (IntegralBlockComplement.insertLocalBlock G v (fun i => LocalCompletion.residuePrime (v i) = q)) :
        Set (IntegralBlockComplement.localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q)))) :
    IsOpen (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  apply PrimeBlockDecomposition.local_subgroup_isOpen_of_primeBlock_neighborhoods G v
    (Finset.univ.image (fun i => LocalCompletion.residuePrime (v i)))
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) H
  intro q hq
  let p := fun i => LocalCompletion.residuePrime (v i) = q
  let J := H.comap (IntegralBlockComplement.insertLocalBlock G v p)
  have hJ : (J : Set (IntegralBlockComplement.localBlockPoints G v p)) ∈ 𝓝 1 := (hblock q hq).mem_nhds J.one_mem
  have ht := (IntegralBlockComplement.restrictLocalBlock_continuous G v p).tendsto (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))
  rw [map_one] at ht
  filter_upwards [ht hJ] with g hg
  change IntegralBlockComplement.insertLocalBlock G v p (IntegralBlockComplement.restrictLocalBlock G v p g) ∈ H at hg
  exact IntegralBlockComplement.insert_restrict_primeBlock G v q g ▸ hg

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductBlockOpenness
