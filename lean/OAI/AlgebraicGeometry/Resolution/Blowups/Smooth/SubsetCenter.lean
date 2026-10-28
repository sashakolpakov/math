import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup

/-! # Subset Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter.Construction

noncomputable section

/-! The selected coordinate centers themselves are smooth affine spaces. -/

open _root_.MvPolynomial

universe u

variable {σ R : Type u} [CommRing R] [DecidableEq σ]

abbrev subsetCoordinateCenterRing (C : Finset σ) := MvPolynomial σ R ⧸ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C

def deleteCenterCoordinates (C : Finset σ) : MvPolynomial σ R →+* MvPolynomial {j : σ // j ∉ C} R :=
  eval₂Hom MvPolynomial.C (fun j => if hj : j ∈ C then 0 else X ⟨j, hj⟩)

theorem deleteCenterCoordinates_C (C : Finset σ) (r : R) :
    deleteCenterCoordinates C (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [deleteCenterCoordinates]

theorem deleteCenterCoordinates_X_in (C : Finset σ) (j : σ) (hj : j ∈ C) :
    deleteCenterCoordinates (R := R) C (X j) = 0 := by
  simp [deleteCenterCoordinates, hj]

theorem deleteCenterCoordinates_X_out (C : Finset σ) (j : σ) (hj : j ∉ C) :
    deleteCenterCoordinates (R := R) C (X j) = X ⟨j, hj⟩ := by
  simp [deleteCenterCoordinates, hj]

def subsetCenterToPolynomial (C : Finset σ) :
    subsetCoordinateCenterRing (R := R) C →+* MvPolynomial {j : σ // j ∉ C} R :=
  Ideal.Quotient.lift _ (deleteCenterCoordinates C) (by
    change SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C ≤ RingHom.ker (deleteCenterCoordinates (R := R) C)
    apply Ideal.span_le.mpr
    rintro p ⟨j, hj, rfl⟩
    exact deleteCenterCoordinates_X_in C j hj)

theorem subsetCenterToPolynomial_mk (C : Finset σ) (p : MvPolynomial σ R) :
    subsetCenterToPolynomial C (Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) p) =
      deleteCenterCoordinates C p := rfl

def polynomialToSubsetCenter (C : Finset σ) :
    MvPolynomial {j : σ // j ∉ C} R →+* subsetCoordinateCenterRing (R := R) C :=
  eval₂Hom ((Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)).comp MvPolynomial.C)
    (fun j => Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (X j.val))

omit [DecidableEq σ] in
theorem polynomialToSubsetCenter_C (C : Finset σ) (r : R) :
    polynomialToSubsetCenter C (MvPolynomial.C r) =
      Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (MvPolynomial.C r) := by
  simp [polynomialToSubsetCenter]

omit [DecidableEq σ] in
theorem polynomialToSubsetCenter_X (C : Finset σ) (j : {j : σ // j ∉ C}) :
    polynomialToSubsetCenter (R := R) C (X j) = Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (X j.val) := by
  simp [polynomialToSubsetCenter]

theorem subsetCenterToPolynomial_fromPolynomial (C : Finset σ) :
    (subsetCenterToPolynomial (R := R) C).comp (polynomialToSubsetCenter C) =
      RingHom.id (MvPolynomial {j : σ // j ∉ C} R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, polynomialToSubsetCenter_C, subsetCenterToPolynomial_mk,
      deleteCenterCoordinates_C]
    rfl
  · intro j
    rw [RingHom.comp_apply, polynomialToSubsetCenter_X, subsetCenterToPolynomial_mk,
      deleteCenterCoordinates_X_out C j.val j.property]
    rfl

theorem polynomialToSubsetCenter_toPolynomial (C : Finset σ) :
    (polynomialToSubsetCenter (R := R) C).comp (subsetCenterToPolynomial C) =
      RingHom.id (subsetCoordinateCenterRing (R := R) C) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change polynomialToSubsetCenter C
      (subsetCenterToPolynomial C (Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (MvPolynomial.C r))) = _
    rw [subsetCenterToPolynomial_mk, deleteCenterCoordinates_C, polynomialToSubsetCenter_C]
    rfl
  · intro j
    change polynomialToSubsetCenter C
      (subsetCenterToPolynomial C (Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (X j))) = _
    rw [subsetCenterToPolynomial_mk]
    by_cases hj : j ∈ C
    · rw [deleteCenterCoordinates_X_in C j hj, map_zero]
      have hz : Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) (X j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, hj, rfl⟩)
      exact hz.symm
    · rw [deleteCenterCoordinates_X_out C j hj, polynomialToSubsetCenter_X]
      rfl

/-- The actual center quotient is polynomial in precisely the unselected coordinates. -/
def subsetCoordinateCenterAlgEquiv (C : Finset σ) :
    subsetCoordinateCenterRing (R := R) C ≃ₐ[R] MvPolynomial {j : σ // j ∉ C} R where
  __ := RingEquiv.ofRingHom (subsetCenterToPolynomial C) (polynomialToSubsetCenter C)
    (subsetCenterToPolynomial_fromPolynomial C) (polynomialToSubsetCenter_toPolynomial C)
  commutes' r := deleteCenterCoordinates_C C r

/-- The center chosen by the monomial rule is smooth over the coefficient base. -/
theorem subsetCoordinateCenter_smooth [Finite σ] (C : Finset σ) :
    Algebra.Smooth R (subsetCoordinateCenterRing (R := R) C) := by
  let : Algebra.Smooth R (MvPolynomial {j : σ // j ∉ C} R) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (subsetCoordinateCenterAlgEquiv C).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter.Construction
