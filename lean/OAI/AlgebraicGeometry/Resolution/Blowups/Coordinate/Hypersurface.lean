import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.AtVariable
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Polynomial.Quotient

/-! # Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface.Construction

noncomputable section

/-! Smoothness of the actual hypersurface quotient in an étale coordinate neighborhood. -/

open _root_.Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An étale map remains étale after quotienting the base and its extended ideal. -/
theorem etale_quotient_of_etale [Algebra R S] [Algebra.Etale R S] (I : Ideal R) :
    Algebra.Etale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm

/-- The zero coordinate hypersurface in an affine line is its base. -/
theorem polynomial_quotient_X_etale : Algebra.Etale R (R[X] ⧸ Ideal.span {(X : R[X])}) := by
  have e : (R[X] ⧸ Ideal.span {(X : R[X])}) ≃ₐ[R] R := by
    have h : Ideal.span {(X : R[X])} = Ideal.span {X - C (0 : R)} := by
      rw [C_0, sub_zero]
    exact (Ideal.quotientEquivAlgOfEq R h).trans (quotientSpanXSubCAlgEquiv (0 : R))
  exact Algebra.Etale.of_equiv e.symm

/-- The equation in the coordinate neighborhood cuts out an étale algebra
over the remaining coordinates. This is the actual quotient used by the coefficient ideals. -/
theorem polynomialCoordinateHypersurface_etale (p : R[X]) :
    Algebra.Etale R
      (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ Ideal.span {PolynomialEtale.Construction.polynomialCoordinateAmbientMap p p}) := by
  let I : Ideal R[X] := Ideal.span {X}
  let : Algebra.Etale R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p) := PolynomialEtale.Construction.polynomialCoordinateChart_etale p
  let : Algebra.Etale R (R[X] ⧸ I) := polynomial_quotient_X_etale
  let : Algebra.Etale (R[X] ⧸ I)
      (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ I.map (algebraMap R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p))) :=
    etale_quotient_of_etale I
  let : IsScalarTower R (R[X] ⧸ I)
      (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ I.map (algebraMap R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p))) := by
    apply IsScalarTower.of_algebraMap_eq (R := R) (S := R[X] ⧸ I)
      (A := PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ I.map (algebraMap R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p)))
    intro r
    rw [IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ I),
      ← IsScalarTower.algebraMap_apply R[X] (R[X] ⧸ I)]
    exact IsScalarTower.algebraMap_apply R R[X] _ r
  let : Algebra.Etale R
      (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ I.map (algebraMap R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p))) :=
    Algebra.Etale.comp R (R[X] ⧸ I) _
  have he : I.map (algebraMap R[X] (PolynomialEtale.Construction.polynomialCoordinateChart p)) =
      Ideal.span {PolynomialEtale.Construction.polynomialCoordinateAmbientMap p p} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton, PolynomialEtale.Construction.polynomialCoordinateChart_coordinate]
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq R he)

variable {σ K : Type*} [Field K] [Finite σ]

/-- The hypersurface in an arbitrary selected-variable coordinate neighborhood
is smooth over the ground field. -/
theorem coordinateHypersurfaceAtVariable_smooth (q : MvPolynomial σ K) (i : σ) :
    Algebra.Smooth K
      (AtVariable.Construction.coordinateChartAtVariable q i ⧸ Ideal.span {AtVariable.Construction.coordinateAmbientMapAtVariable q i q}) := by
  let : Fintype {j : σ // j ≠ i} := Fintype.ofFinite _
  let : Algebra.Smooth K (MvPolynomial {j : σ // j ≠ i} K) := ⟨inferInstance, inferInstance⟩
  let p := MvPolynomial.optionEquivLeft K {j : σ // j ≠ i} (AtVariable.Construction.separateVariableEquiv i q)
  let : Algebra.Etale (MvPolynomial {j : σ // j ≠ i} K)
      (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ Ideal.span {PolynomialEtale.Construction.polynomialCoordinateAmbientMap p p}) :=
    polynomialCoordinateHypersurface_etale p
  exact Algebra.Smooth.comp K (MvPolynomial {j : σ // j ≠ i} K)
    (PolynomialEtale.Construction.polynomialCoordinateChart p ⧸ Ideal.span {PolynomialEtale.Construction.polynomialCoordinateAmbientMap p p})

omit [Finite σ] in
/-- A point satisfying the equation with nonzero selected partial derivative
lifts to the same smooth quotient used for coefficient ideals. -/
theorem coordinateHypersurfaceAtVariable_has_point
    (q : MvPolynomial σ K) (i : σ) (x : σ → K)
    (hq : MvPolynomial.eval x q = 0) (hi : MvPolynomial.eval x (MvPolynomial.pderiv i q) ≠ 0) :
    ∃ e : (AtVariable.Construction.coordinateChartAtVariable q i ⧸ Ideal.span {AtVariable.Construction.coordinateAmbientMapAtVariable q i q}) →+* K,
      ∀ r : MvPolynomial σ K,
        e (Ideal.Quotient.mk (Ideal.span {AtVariable.Construction.coordinateAmbientMapAtVariable q i q})
          (AtVariable.Construction.coordinateAmbientMapAtVariable q i r)) = MvPolynomial.eval x r := by
  obtain ⟨e, he⟩ := AtVariable.Construction.coordinateChartAtVariable_has_point q i x hi
  have hzero : ∀ s ∈ Ideal.span {AtVariable.Construction.coordinateAmbientMapAtVariable q i q}, e s = 0 := by
    intro s hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hs
    rw [ht, map_mul, he, hq, zero_mul]
  exact ⟨Ideal.Quotient.lift _ e hzero, he⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface.Construction
