import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFreeRank
import OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomial

/-! # Mv Polynomial Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomialRank

noncomputable section

/-! Coordinate n-th powers on affine d-space have finite-free rank n^d. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

theorem mvPolynomial_expand_hasFiniteBasis (hn : n ≠ 0) (σ : Type v) [Finite σ] :
    FiniteFreeRank.Construction.RingHomHasFiniteBasis (MvPolynomial.expand n (R := R) (σ := σ)).toRingHom
      (n ^ Nat.card σ) := by
  refine Finite.induction_empty_option
    (P := fun α => FiniteFreeRank.Construction.RingHomHasFiniteBasis (MvPolynomial.expand n (R := R) (σ := α)).toRingHom
      (n ^ Nat.card α)) ?_ ?_ ?_ σ
  · intro α β e hα
    let E := MvPolynomial.renameEquiv R e
    have he : E.toRingHom.comp (MvPolynomial.expand n (R := R) (σ := α)).toRingHom =
        (MvPolynomial.expand n (R := R) (σ := β)).toRingHom.comp E.toRingHom := by
      ext r <;> simp [E]
    have hc := hα.comp (FiniteFreeRank.Construction.ringHomHasFiniteBasis_of_bijective E.toRingHom E.bijective)
    rw [he, mul_one] at hc
    have hβ := hc.of_comp_bijective_right E.bijective
    rwa [Nat.card_congr e] at hβ
  · have he : (MvPolynomial.expand n (R := R) (σ := PEmpty.{v + 1})).toRingHom =
        RingHom.id _ := by
      ext r
      · simp
      · cases r
    rw [he]
    simpa using FiniteFreeRank.Construction.ringHomHasFiniteBasis_of_bijective
      (RingHom.id (MvPolynomial PEmpty R)) Function.bijective_id
  · intro α _ hα
    let E := MvPolynomial.optionEquivLeft R α
    let P := Polynomial.mapRingHom (MvPolynomial.expand n (R := R) (σ := α)).toRingHom
    let Q := (Polynomial.expand (MvPolynomial α R) n).toRingHom
    have he : E.toRingHom.comp (MvPolynomial.expand n (R := R) (σ := Option α)).toRingHom =
        (Q.comp P).comp E.toRingHom := by
      ext r
      · simp [E, P, Q]
      · cases r <;> simp [E, P, Q]
    have hP : FiniteFreeRank.Construction.RingHomHasFiniteBasis P (n ^ Nat.card α) := hα.polynomial
    have hQ : FiniteFreeRank.Construction.RingHomHasFiniteBasis Q n := FiniteFreeRank.Construction.polynomial_expand_hasFiniteBasis (MvPolynomial α R) n hn
    have hc := (FiniteFreeRank.Construction.ringHomHasFiniteBasis_of_bijective E.toRingHom E.bijective).comp (hP.comp hQ)
    rw [← he, one_mul] at hc
    have hOption := hc.of_comp_bijective_left E.bijective
    let := Fintype.ofFinite α
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option, pow_succ] using hOption

theorem mvPolynomial_expand_finrank (hn : n ≠ 0) (σ : Type v) [Finite σ]
    (x : PrimeSpectrum (MvPolynomial σ R)) :
    (MvPolynomial.expand n (R := R) (σ := σ)).toRingHom.finrank x = n ^ Nat.card σ :=
  (mvPolynomial_expand_hasFiniteBasis R n hn σ).finrank x

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomialRank
