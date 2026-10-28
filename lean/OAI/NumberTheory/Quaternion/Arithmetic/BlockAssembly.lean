import OAI.NumberTheory.Quaternion.Arithmetic.BlockComplement
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockCompactProjection
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteProductBlockOpenness

/-! # Block Assembly -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.BlockAssembly

noncomputable section

/-! Arithmetic closure in an arbitrary finite local product is open
once the arithmetic closures in its residue-prime blocks are open. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem arithmeticBlockComplementEmbedding_mem_closure
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S U : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (g : Groups.sIntegralPoints G (BlockComplement.arithmeticBlockPlaces S v p : Set (LocalAdeles.Place F))) :
    IntegralBlockComplement.insertIntegralBlockComplement G v p (BlockComplement.arithmeticBlockComplementEmbedding G S v p hinj haway g) ∈
      (Product.arithmeticProductSubgroup G U v).topologicalClosure := by
  rw [BlockComplement.arithmeticBlockComplementEmbedding_insert]
  apply (Product.arithmeticProductSubgroup G U v).le_topologicalClosure
  refine ⟨g.val, ?_, rfl⟩
  exact Groups.sIntegralPoints_mono G (BlockComplement.arithmeticBlockPlaces_subset S U v p hSU hU) g.property

theorem arithmetic_closure_isOpen_of_primeBlock_closures
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S U : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F))
    (hinj : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U)
    (hblock : ∀ q ∈ Finset.univ.image (fun i => LocalCompletion.residuePrime (v i)),
      IsOpen ((Product.arithmeticProductSubgroup G (BlockComplement.arithmeticBlockPlaces S v (fun i => LocalCompletion.residuePrime (v i) = q))
        (fun i : {i : ι // LocalCompletion.residuePrime (v i) = q} => v i.val)).topologicalClosure :
          Set (IntegralBlockComplement.localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q)))) :
    IsOpen ((Product.arithmeticProductSubgroup G U v).topologicalClosure :
      Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  let H := (Product.arithmeticProductSubgroup G U v).topologicalClosure
  apply FiniteProductBlockOpenness.local_product_isOpen_of_block_comaps G v H
  intro q hq
  obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp hq
  let p := fun i => LocalCompletion.residuePrime (v i) = q
  let e := BlockComplement.arithmeticBlockComplementEmbedding G S v p hinj haway
  apply PrimeBlockCompactProjection.primeBlock_comap_isOpen_of_open_compact_projection G v (v i₀) q hi₀ H
    (Product.arithmeticProductSubgroup G U v).isClosed_topologicalClosure e.range
  · rintro x ⟨g, rfl⟩
    exact arithmeticBlockComplementEmbedding_mem_closure G S U v p hinj haway hSU hU g
  · have he := BlockComplement.arithmeticBlockComplementEmbedding_projection_range G S v p hinj haway
    change IsOpen ((e.range.map (MonoidHom.snd _ _)).topologicalClosure : Set (IntegralBlockComplement.localBlockPoints G v p))
    rw [he]
    exact hblock q (Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, hi₀⟩)

end

end OAI.NumberTheory.Quaternion.Arithmetic.BlockAssembly
