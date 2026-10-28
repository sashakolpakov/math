import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polynomial
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fintype.Option

/-! # Mv Polynomial -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomial.Construction

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Simultaneously raising finitely many polynomial coordinates to a
positive power gives a flat ring map over an arbitrary coefficient ring. -/
theorem mvPolynomial_expand_flat (hn : n ≠ 0) (σ : Type v) [Finite σ] :
    (MvPolynomial.expand n (R := R) (σ := σ)).toRingHom.Flat := by
  refine Finite.induction_empty_option
    (P := fun α => (MvPolynomial.expand n (R := R) (σ := α)).toRingHom.Flat)
    ?_ ?_ ?_ σ
  · intro α β e hα
    let E := MvPolynomial.renameEquiv R e
    have he : E.toRingHom.comp (MvPolynomial.expand n (R := R) (σ := α)).toRingHom =
        (MvPolynomial.expand n (R := R) (σ := β)).toRingHom.comp E.toRingHom := by
      ext r <;> simp [E]
    apply (RingHom.Flat.comp_iff_of_bijective_right E.bijective).mp
    erw [← he]
    exact hα.comp (RingHom.Flat.of_bijective E.bijective)
  · have he : (MvPolynomial.expand n (R := R) (σ := PEmpty.{v + 1})).toRingHom =
        RingHom.id _ := by
      ext r
      · simp
      · cases r
    rw [he]
    exact RingHom.Flat.id _
  · intro α _ hα
    let E := MvPolynomial.optionEquivLeft R α
    let P := Polynomial.mapRingHom (MvPolynomial.expand n (R := R) (σ := α)).toRingHom
    let Q := (Polynomial.expand (MvPolynomial α R) n).toRingHom
    have he : E.toRingHom.comp
        (MvPolynomial.expand n (R := R) (σ := Option α)).toRingHom =
          (Q.comp P).comp E.toRingHom := by
      ext r
      · simp [E, P, Q]
      · cases r <;> simp [E, P, Q]
    apply (RingHom.Flat.comp_iff_of_bijective_left E.bijective).mp
    erw [he]
    exact (RingHom.Flat.of_bijective E.bijective).comp
      ((Homomorphisms.Polynomial.Construction.polynomial_map_flat (MvPolynomial α R) _ hα).comp
        (Homomorphisms.Polynomial.Construction.polynomial_expand_flat (MvPolynomial α R) n hn))

end OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomial.Construction
