import OAI.NumberTheory.Quaternion.Arithmetic.IntegralComplement
import OAI.NumberTheory.Quaternion.Arithmetic.Closure

/-! # Complement -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Complement

noncomputable section

/-! Rational points integral away from S and one selected place lie in
the compact integral groups at every other selected place. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

theorem singlePlaceArithmetic_integral_elsewhere (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    (g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))))
    (j : {j : ι // j ≠ i}) : LocalAdeles.diagonalLocal G (Sum.inr (v j.val)) g.val ∈
      LocalAdeles.integralLocalSubgroup G (Sum.inr (v j.val)) := by
  apply g.property
  rintro (he | hs)
  · exact j.property (hv (Sum.inr.inj he))
  · exact haway j.val hs

def arithmeticComplementEmbedding (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι) :
    Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))) →*
      (IntegralComplement.integralComplement G v i × LocalAdeles.LocalPoints G (Sum.inr (v i))) where
  toFun g := (fun j => ⟨LocalAdeles.diagonalLocal G (Sum.inr (v j.val)) g.val,
    singlePlaceArithmetic_integral_elsewhere G S v hv haway i g j⟩,
    LocalAdeles.diagonalLocal G (Sum.inr (v i)) g.val)
  map_one' := by
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact map_one _
    · exact map_one _
  map_mul' g h := by
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact map_mul _ _ _
    · exact map_mul _ _ _

theorem arithmeticComplementEmbedding_coordinate (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i j : ι)
    (g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F)))) :
    IntegralComplement.insertIntegralComplement G v i (arithmeticComplementEmbedding G S v hv haway i g) j =
      LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val := by
  by_cases h : j = i
  · subst j
    rw [IntegralComplement.insertIntegralComplement_self]
    rfl
  · simp only [IntegralComplement.insertIntegralComplement, MonoidHom.coe_mk, OneHom.coe_mk, dite_eq_right h,
      arithmeticComplementEmbedding]

theorem arithmeticComplementEmbedding_projection_range (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι) :
    (arithmeticComplementEmbedding G S v hv haway i).range.map
        (MonoidHom.snd (IntegralComplement.integralComplement G v i) (LocalAdeles.LocalPoints G (Sum.inr (v i)))) =
      Closure.localArithmeticSubgroup G (insert (Sum.inr (v i)) S) (Sum.inr (v i)) := by
  rw [MonoidHom.map_range]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.val, ?_, rfl⟩
    change g.val ∈ Groups.sIntegralPoints G (↑(insert (Sum.inr (v i)) S))
    rw [Finset.coe_insert]
    exact g.property
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, ?_⟩, rfl⟩
    change g ∈ Groups.sIntegralPoints G (↑(insert (Sum.inr (v i)) S)) at hg
    rw [Finset.coe_insert] at hg
    exact hg

end

end OAI.NumberTheory.Quaternion.Arithmetic.Complement
