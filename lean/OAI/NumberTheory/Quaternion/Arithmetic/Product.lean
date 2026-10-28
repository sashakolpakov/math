import OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentTo
import OAI.NumberTheory.Quaternion.Arithmetic.TangentInclusion

/-! # Product -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Product

noncomputable section

/-! Rational commensurability and single-place arithmetic inclusions for
the actual simultaneous S-integral local product. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

def diagonalFiniteProduct (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F)) :
    G.RationalPoints →* (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) where
  toFun g i := LocalAdeles.diagonalLocal G (Sum.inr (v i)) g
  map_one' := by funext i; exact map_one _
  map_mul' g h := by funext i; exact map_mul _ _ _

theorem diagonalFiniteProduct_injective [Nonempty ι]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F)) :
    Function.Injective (diagonalFiniteProduct G v) := by
  intro g h he
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact LocalAdeles.diagonalLocal_injective G (Sum.inr (v i)) (congrFun he i)

def arithmeticProductSubgroup (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (U : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F)) :
    Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :=
  (Groups.sIntegralPoints G (U : Set (LocalAdeles.Place F))).map (diagonalFiniteProduct G v)

theorem arithmeticProduct_conjugate_commensurable [Nonempty ι]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (U : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hU : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ U) (g : G.RationalPoints) :
    ((arithmeticProductSubgroup G U v).map
      (MulAut.conj (diagonalFiniteProduct G v g)).toMonoidHom).Commensurable
        (arithmeticProductSubgroup G U v) := by
  have h := Closure.commensurable_map_of_injective (diagonalFiniteProduct G v)
    (diagonalFiniteProduct_injective G v) (Commensurability.sIntegralPoints_conjugate_commensurable G U hU g⁻¹)
  rw [Closure.map_comap_conj, map_inv, Subgroup.comap_equiv_eq_map_symm'] at h
  have he : (MulAut.conj (diagonalFiniteProduct G v g)⁻¹).symm.toMonoidHom =
      (MulAut.conj (diagonalFiniteProduct G v g)).toMonoidHom := by
    ext x
    simp
  rw [he] at h
  exact h

theorem singlePlaceArithmetic_mem_product (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S U : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hSU : S ⊆ U) (i : ι) (hi : Sum.inr (v i) ∈ U)
    (g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F)))) :
    diagonalFiniteProduct G v g.val ∈ arithmeticProductSubgroup G U v := by
  refine ⟨g.val, ?_, rfl⟩
  apply Groups.sIntegralPoints_mono G _ g.property
  rintro w (he | hw)
  · exact he ▸ hi
  · exact hSU hw

end

end OAI.NumberTheory.Quaternion.Arithmetic.Product
