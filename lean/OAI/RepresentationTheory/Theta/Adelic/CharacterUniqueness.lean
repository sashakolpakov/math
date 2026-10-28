import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation

/-! # Character Uniqueness -/

namespace OAI.RepresentationTheory.Theta.Adelic.CharacterUniqueness

noncomputable section

/-! A continuous adelic character trivial on the number field is
uniquely determined by its archimedean local components. -/

open scoped Classical _root_.NumberField

open _root_.NumberField

theorem character_finset_sum {I U : Type*} [AddCommMonoid U]
    (ψ : AddChar U ℂ) (t : Finset I) (u : I → U) :
    ψ (∑ i ∈ t, u i) = ∏ i ∈ t, ψ (u i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

theorem character_product_value {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
    (ψ : AddChar (U × V) ℂ) (a : U) (b : V) :
    ψ (a, b) = ψ (a, 0) * ψ (0, b) := by
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using ψ.map_add_eq_mul (a, 0) (0, b)

variable (F : Type) [Field F] [NumberField F]

theorem infinite_adele_local_sum (a : InfiniteAdeleRing F) :
    (∑ v : InfinitePlace F, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) (a v)) = ((a, 0) : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) := by
  change (∑ v : InfinitePlace F, (Pi.single v (a v), (0 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))) = (a, 0)
  rw [← prod_mk_sum, Finset.sum_const_zero]
  congr 1
  funext v
  rw [Finset.sum_apply]
  exact Fintype.sum_pi_single v a

theorem adelic_characters_eq_of_archimedean
    (ψ η : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hψ : Continuous ψ) (hη : Continuous η)
    (hn : ∀ a, ψ a ≠ 0)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (hq : ∀ q : F, η (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (hl : ∀ (v : InfinitePlace F) (t : v.Completion),
      Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t = Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F η (.inl v) t) : ψ = η := by
  have hi (a : InfiniteAdeleRing F) : ψ (a, 0) = η (a, 0) := by
    rw [← infinite_adele_local_sum F a, character_finset_sum, character_finset_sum]
    exact Finset.prod_congr rfl (fun v _ => hl v (a v))
  have hfr (q : F) : ψ (0, algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = η (0, algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) := by
    let a := algebraMap F (InfiniteAdeleRing F) q
    let b := algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q
    have hp' : ψ (a, 0) * ψ (0, b) = 1 := (character_product_value ψ a b).symm.trans (hp q)
    have hq' : η (a, 0) * η (0, b) = 1 := (character_product_value η a b).symm.trans (hq q)
    apply mul_left_cancel₀ (hn (a, 0))
    exact hp'.trans ((congrArg (fun c => c * η (0, b)) (hi a)).trans hq').symm
  have hf : (fun b : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => ψ (0, b)) = (fun b => η (0, b)) :=
    (Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).equalizer
      (hψ.comp (continuous_const.prodMk continuous_id))
      (hη.comp (continuous_const.prodMk continuous_id)) (funext hfr)
  ext a
  rcases a with ⟨a, b⟩
  exact (character_product_value ψ a b).trans
    ((congrArg₂ (fun x y : ℂ => x * y) (hi a) (congrFun hf b)).trans
      (character_product_value η a b).symm)

end

end OAI.RepresentationTheory.Theta.Adelic.CharacterUniqueness
