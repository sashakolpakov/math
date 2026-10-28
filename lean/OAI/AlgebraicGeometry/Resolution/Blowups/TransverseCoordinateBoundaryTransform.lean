import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTransformIdeals
import Mathlib.Algebra.MvPolynomial.Division

/-! # Transverse Coordinate Boundary Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinateBoundaryTransform.Construction

noncomputable section

/-! A boundary coordinate transverse to a coordinate center is unchanged by control-one ideal quotient. -/

open _root_.MvPolynomial

universe u

theorem ideal_map_equiv_injective {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Function.Injective (Ideal.map e.toRingHom) := by
  intro I J h
  apply Ideal.comap_injective_of_surjective e.symm.toRingHom e.symm.surjective
  exact (Ideal.map_comap_of_equiv e).symm.trans (h.trans (Ideal.map_comap_of_equiv e))

theorem coordinate_principal_colon_distinct
    {k σ : Type u} [CommRing k] [IsDomain k] (i j : σ) (hji : j ≠ i) :
    (Ideal.span {(X j : MvPolynomial σ k)}).colon
      (Ideal.span {(X i : MvPolynomial σ k)} : Set (MvPolynomial σ k)) = Ideal.span {X j} := by
  ext p
  simp only [Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton,
    (X_prime (R := k) (i := j)).dvd_mul, X_dvd_X, hji, or_false]

theorem subsetCoordinateBlowupChartEquiv_constants
    {k σ : Type u} [CommRing k] [DecidableEq σ] (C : Finset σ) (i : C) (p : MvPolynomial σ k) :
    SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChartEquiv (R := k) C i
      (Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i) p) =
        SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution (R := k) C i p :=
  SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial_constants C i p

theorem principal_colon_of_equiv_coordinates
    {A k σ : Type u} [CommRing A] [CommRing k] [IsDomain k]
    (e : A ≃+* MvPolynomial σ k) (a c : A) (i j : σ) (hji : j ≠ i)
    (ha : e a = X j) (hc : e c = X i) :
    (Ideal.span {a}).colon (Ideal.span {c} : Set A) = Ideal.span {a} := by
  apply ideal_map_equiv_injective e
  rw [PolynomialTransformIdeals.Construction.map_colon_principal_equiv]
  simp only [Ideal.map_span, Set.image_singleton]
  change (Ideal.span {e a}).colon (Ideal.span {e c} : Set (MvPolynomial σ k)) = Ideal.span {e a}
  rw [ha, hc]
  exact coordinate_principal_colon_distinct i j hji

theorem subsetCoordinateBlowup_transverse_boundary_controlled
    {k σ : Type u} [CommRing k] [IsDomain k] [DecidableEq σ]
    (C : Finset σ) (i : C) (j : σ) (hj : j ∉ C) :
    ControlledTransform.Construction.blowupControlledTransform (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C) (Ideal.span {X j}) 1 (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i) =
      Ideal.span {Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i) (X j)} := by
  rw [ControlledTransform.Construction.blowupControlledTransform, Ideal.map_span, Set.image_singleton]
  rw [pow_one (Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C)
    (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := k) C i).val)]
  apply principal_colon_of_equiv_coordinates (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChartEquiv (R := k) C i)
    _ _ i.val j (fun h => hj (h.symm ▸ i.property))
  · exact (subsetCoordinateBlowupChartEquiv_constants C i (X j)).trans
      (SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_outside C i j hj)
  · exact (subsetCoordinateBlowupChartEquiv_constants C i (X i.val)).trans
      (SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_self C i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseCoordinateBoundaryTransform.Construction
