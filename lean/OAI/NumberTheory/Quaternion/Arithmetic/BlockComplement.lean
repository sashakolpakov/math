import OAI.NumberTheory.Quaternion.Arithmetic.Product
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralBlockComplement

/-! # Block Complement -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.BlockComplement

noncomputable section

/-! Actual S-integral arithmetic points for a selected block have
integral coordinates in its complement, with exactly the expected
arithmetic subgroup as their projection to the block. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

def arithmeticBlockPlaces (S : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) : Finset (LocalAdeles.Place F) :=
  S ∪ Finset.univ.image (fun i : {i : ι // p i} => Sum.inr (v i.val))

omit [NumberField F] in
theorem arithmeticBlockPlaces_contains_base (S : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) : S ⊆ arithmeticBlockPlaces S v p :=
  Finset.subset_union_left

omit [NumberField F] in
theorem arithmeticBlockPlaces_contains_block (S : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) (i : {i : ι // p i}) :
    Sum.inr (v i.val) ∈ arithmeticBlockPlaces S v p :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

omit [NumberField F] in
theorem arithmeticBlockPlaces_subset (S U : Finset (LocalAdeles.Place F))
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hSU : S ⊆ U) (hU : ∀ i, Sum.inr (v i) ∈ U) : arithmeticBlockPlaces S v p ⊆ U := by
  intro w hw
  rcases Finset.mem_union.mp hw with hs | hb
  · exact hSU hs
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact hU i.val

theorem arithmeticBlock_integral_elsewhere (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hv : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (g : Groups.sIntegralPoints G (arithmeticBlockPlaces S v p : Set (LocalAdeles.Place F)))
    (i : {i : ι // ¬ p i}) : LocalAdeles.diagonalLocal G (Sum.inr (v i.val)) g.val ∈
      LocalAdeles.integralLocalSubgroup G (Sum.inr (v i.val)) := by
  apply g.property
  intro hi
  rcases Finset.mem_union.mp hi with hs | hb
  · exact haway i.val hs
  · obtain ⟨j, _, he⟩ := Finset.mem_image.mp hb
    exact i.property ((hv (Sum.inr.inj he)) ▸ j.property)

def arithmeticBlockComplementEmbedding (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hv : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S) :
    Groups.sIntegralPoints G (arithmeticBlockPlaces S v p : Set (LocalAdeles.Place F)) →*
      (IntegralBlockComplement.integralBlockComplement G v p × IntegralBlockComplement.localBlockPoints G v p) where
  toFun g := (fun i => ⟨LocalAdeles.diagonalLocal G (Sum.inr (v i.val)) g.val,
    arithmeticBlock_integral_elsewhere G S v p hv haway g i⟩,
    fun i => LocalAdeles.diagonalLocal G (Sum.inr (v i.val)) g.val)
  map_one' := by
    apply Prod.ext
    · funext i; apply Subtype.ext; exact map_one _
    · funext i; exact map_one _
  map_mul' g h := by
    apply Prod.ext
    · funext i; apply Subtype.ext; exact map_mul _ _ _
    · funext i; exact map_mul _ _ _

theorem arithmeticBlockComplementEmbedding_insert (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hv : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S)
    (g : Groups.sIntegralPoints G (arithmeticBlockPlaces S v p : Set (LocalAdeles.Place F))) :
    IntegralBlockComplement.insertIntegralBlockComplement G v p (arithmeticBlockComplementEmbedding G S v p hv haway g) =
      Product.diagonalFiniteProduct G v g.val := by
  funext i
  by_cases hi : p i <;>
    simp [IntegralBlockComplement.insertIntegralBlockComplement, arithmeticBlockComplementEmbedding, Product.diagonalFiniteProduct, hi]

theorem arithmeticBlockComplementEmbedding_projection_range (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop)
    (hv : Function.Injective v) (haway : ∀ i, Sum.inr (v i) ∉ S) :
    (arithmeticBlockComplementEmbedding G S v p hv haway).range.map (MonoidHom.snd _ _) =
      Product.arithmeticProductSubgroup G (arithmeticBlockPlaces S v p) (fun i : {i : ι // p i} => v i.val) := by
  rw [MonoidHom.map_range]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, g.property, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.BlockComplement
