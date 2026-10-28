import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Tactic

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Polynomial.Construction

open _root_.Polynomial

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A monic presentation for adjoining an n-th root of the coordinate. -/
noncomputable def expansionPolynomial : Polynomial (Polynomial R) := X ^ n - C X

noncomputable def expansionLift : AdjoinRoot (expansionPolynomial R n) →+* R[X] :=
  AdjoinRoot.lift (expand R n).toRingHom X (by
    simp [expansionPolynomial, Polynomial.expand_X])

noncomputable def expansionInverse : R[X] →+* AdjoinRoot (expansionPolynomial R n) :=
  Polynomial.eval₂RingHom ((AdjoinRoot.of (expansionPolynomial R n)).comp C)
    (AdjoinRoot.root (expansionPolynomial R n))

set_option backward.isDefEq.respectTransparency.types false in
theorem expansion_root_pow :
    AdjoinRoot.root (expansionPolynomial R n) ^ n =
      AdjoinRoot.of (expansionPolynomial R n) X := by
  have h := AdjoinRoot.eval₂_root (expansionPolynomial R n)
  apply sub_eq_zero.mp
  unfold expansionPolynomial at h
  erw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact h

theorem expansionLift_inverse :
    (expansionLift R n).comp (expansionInverse R n) = RingHom.id _ := by
  ext r <;> simp [expansionLift, expansionInverse]

theorem expansionInverse_lift :
    (expansionInverse R n).comp (expansionLift R n) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · ext r <;> simp [expansionLift, expansionInverse, Polynomial.expand_X,
      expansion_root_pow]
  · simp [expansionLift, expansionInverse]

/-- The displayed monic root algebra is the polynomial ring, with its
coefficient map acting by expansion of the coordinate. -/
noncomputable def expansionEquiv : AdjoinRoot (expansionPolynomial R n) ≃+* R[X] :=
  RingEquiv.ofRingHom (expansionLift R n) (expansionInverse R n)
    (expansionLift_inverse R n) (expansionInverse_lift R n)

/-- The coordinate power map on the affine line is flat over every base ring. -/
theorem polynomial_expand_flat (hn : n ≠ 0) : (expand R n).toRingHom.Flat := by
  have hmonic : (expansionPolynomial R n).Monic := monic_X_pow_sub_C X hn
  have : Module.Free R[X] (AdjoinRoot (expansionPolynomial R n)) := hmonic.free_adjoinRoot
  have hflat : (AdjoinRoot.of (expansionPolynomial R n)).Flat := by
    change (algebraMap R[X] (AdjoinRoot (expansionPolynomial R n))).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hlift : (expansionLift R n).Flat :=
    RingHom.Flat.of_bijective (expansionEquiv R n).bijective
  have hcomp := hflat.comp hlift
  simpa only [expansionLift, AdjoinRoot.lift_comp_of] using hcomp

/-- Extending a flat coefficient map to polynomial rings remains flat. -/
theorem polynomial_map_flat {S : Type*} [CommRing S]
    (f : R →+* S) (hf : f.Flat) : (Polynomial.mapRingHom f).Flat := by
  algebraize [f]
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  change (algebraMap R[X] S[X]).Flat
  apply RingHom.flat_algebraMap_iff.mpr
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R R[X] S S[X]).toLinearEquiv.symm

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Polynomial.Construction
