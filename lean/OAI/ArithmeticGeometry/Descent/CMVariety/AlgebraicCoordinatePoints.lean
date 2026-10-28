import OAI.ArithmeticGeometry.Descent.CMVariety.QuasiFinitePoints
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Algebraic Coordinate Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicCoordinatePoints.Abelian

noncomputable section

/-! An affine complex evaluation with algebraic values has closed image.
Consequently points over such coordinates in a quasi-finite arithmetic
chart have actual number-field factorizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem algebraic_evaluation_kernel_maximal {R : Type} [CommRing R] [Algebra ℚ R]
    (x : R →ₐ[ℚ] ℂ) (hx : ∀ r, IsAlgebraic ℚ (x r)) :
    (RingHom.ker x.toRingHom).IsMaximal := by
  have hrange : x.range.IsAlgebraic := by
    rintro z ⟨r, rfl⟩
    exact hx r
  let K := hrange.toIntermediateField
  let y : R →+* K := x.toRingHom.codRestrict K (fun r => x.mem_range_self r)
  have hy : Function.Surjective y := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr⟩ := hz
    exact ⟨r, Subtype.ext hr⟩
  have hker : RingHom.ker y = RingHom.ker x.toRingHom := by
    ext r
    change y r = 0 ↔ x r = 0
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact hker ▸ RingHom.ker_isMaximal_of_surjective y hy

theorem algebraic_affine_evaluation_closed {R : Type} [CommRing R] [Algebra ℚ R]
    (x : R →ₐ[ℚ] ℂ) (hx : ∀ r, IsAlgebraic ℚ (x r)) :
    IsClosed {(Spec.map (CommRingCat.ofHom x.toRingHom)) (IsLocalRing.closedPoint ℂ)} := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  change (Ideal.comap x.toRingHom (IsLocalRing.maximalIdeal ℂ)).IsMaximal
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact algebraic_evaluation_kernel_maximal x hx

theorem polynomial_evaluation_algebraic {Index : Type*} (x : Index → ℂ)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) (P : MvPolynomial Index ℚ) :
    IsAlgebraic ℚ (MvPolynomial.aeval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.aeval_C] using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) a)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using hp.mul (hx i)

theorem algebraic_polynomial_evaluation_closed {Index : Type} (x : Index → ℂ)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    IsClosed {(Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℚ) x).toRingHom))
      (IsLocalRing.closedPoint ℂ)} :=
  algebraic_affine_evaluation_closed (MvPolynomial.aeval x) (polynomial_evaluation_algebraic x hx)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicCoordinatePoints.Abelian
