import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Translation Invariant Polynomial Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TranslationInvariantPolynomialIdeal.Construction

noncomputable section

/-! An ideal invariant under every affine translation is either zero or the unit ideal. -/

open _root_.MvPolynomial

theorem eval_polynomialTranslate {σ R : Type*} [CommRing R]
    (x a : σ → R) (p : MvPolynomial σ R) :
    eval x (PolynomialTranslation.Construction.polynomialTranslate a p) = eval (x + a) p := by
  have h : (eval x).comp (PolynomialTranslation.Construction.polynomialTranslate a).toRingHom = eval (x + a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h p

theorem translation_invariant_polynomial_ideal_eq_bot_or_top
    {σ k : Type*} [Finite σ] [Field k] [IsAlgClosed k] [Infinite k]
    (I : Ideal (MvPolynomial σ k))
    (hI : ∀ a : σ → k, I.map (PolynomialTranslation.Construction.polynomialTranslate a).toRingHom ≤ I) : I = ⊥ ∨ I = ⊤ := by
  by_cases ht : I = ⊤
  · exact Or.inr ht
  left
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I ht
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hM
  apply le_bot_iff.mp
  intro p hp
  change p = 0
  apply MvPolynomial.funext
  intro y
  have ht : PolynomialTranslation.Construction.polynomialTranslate (y - x) p ∈ I :=
    hI (y - x) (Ideal.mem_map_of_mem _ hp)
  have hz := MvPolynomial.mem_vanishingIdeal_singleton_iff x _ |>.mp (hx ▸ hIM ht)
  have hxy : x + (y - x) = y := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  simpa only [MvPolynomial.aeval_eq_eval, eval_polynomialTranslate, hxy, map_zero] using hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TranslationInvariantPolynomialIdeal.Construction
