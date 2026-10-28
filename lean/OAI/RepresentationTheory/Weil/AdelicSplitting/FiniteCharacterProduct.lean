import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.Annihilator

/-! # Finite Character Product -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction

noncomputable section

/-! Product formulas for the actual finite-adelic additive character and
the rational phase identity used in shifted Poisson summation. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

def finiteAdelicCharacter (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) : AddChar (ArchimedeanAdeles.Construction.FiniteAdeles F) ℂ :=
  ψ.compAddMonoidHom (Annihilator.Construction.finiteAdelicAdd F)

theorem localAdditiveCharacter_finite_hasProd (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hc : Continuous ψ) (a : ArchimedeanAdeles.Construction.FiniteAdeles F) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => Characters.Construction.localAdditiveCharacter F ψ (.inr v) (a v))
      (finiteAdelicCharacter F ψ a) := by
  let f := fun v : ArchimedeanAdeles.Construction.Places F => Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.evaluate F v (Annihilator.Construction.finiteAdelicAdd F a))
  have hall : HasProd f (finiteAdelicCharacter F ψ a) := CharacterProduct.Construction.localAdditiveCharacter_hasProd F ψ hc (Annihilator.Construction.finiteAdelicAdd F a)
  have hout : ∀ v ∉ Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → ArchimedeanAdeles.Construction.Places F), f v = 1 := by
    intro v hv
    cases v with
    | inl v =>
        change Characters.Construction.localAdditiveCharacter F ψ (.inl v) 0 = 1
        exact AddChar.map_zero_eq_one _
    | inr v => exact (hv ⟨v, rfl⟩).elim
  exact (Sum.inr_injective.hasProd_iff hout).mpr hall

theorem finiteAdelicCharacter_principal_negative (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) (q : F) :
    finiteAdelicCharacter F ψ (-algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) =
      ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (mixedEmbedding F q) := by
  have he : Annihilator.Construction.finiteAdelicAdd F (-algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) =
      ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (mixedEmbedding F q) - algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q := by
    rw [ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_rational]
    apply Prod.ext
    · change (0 : InfiniteAdeleRing F) = algebraMap F (InfiniteAdeleRing F) q - algebraMap F (InfiniteAdeleRing F) q
      exact (sub_self _).symm
    · change -algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q = 0 - algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q
      exact (zero_sub _).symm
  change ψ (Annihilator.Construction.finiteAdelicAdd F (-algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q)) = _
  rw [he, ψ.map_sub_eq_div, hp, div_one]
  rfl

theorem localAdditiveCharacter_finite_dot_hasProd (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hc : Continuous ψ) {N : ℕ} (x y : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => Characters.Construction.localAdditiveCharacter F ψ (.inr v)
      (-(∑ i, x i v * y i v))) (finiteAdelicCharacter F ψ (-(∑ i, x i * y i))) := by
  have h := localAdditiveCharacter_finite_hasProd F ψ hc (-(∑ i, x i * y i))
  convert h using 1
  funext v
  congr 1
  let e : ArchimedeanAdeles.Construction.FiniteAdeles F →+* v.adicCompletion F :=
    RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  have he : e (-(∑ i, x i * y i)) = -(∑ i, e (x i) * e (y i)) := by
    simp only [map_neg, map_sum, map_mul]
  exact he.symm

theorem finite_rational_dot_phase (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) {N : ℕ} (x y : Fin N → F) :
    finiteAdelicCharacter F ψ (-(∑ i, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (x i) * algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (y i))) =
      ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F (x i) * mixedEmbedding F (y i)) := by
  simp only [← map_mul, ← map_sum]
  exact finiteAdelicCharacter_principal_negative F ψ hp (∑ i, x i * y i)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction
