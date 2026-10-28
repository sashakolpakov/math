import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup

/-! # Subset Coordinate Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction

noncomputable section

/-! Actual Rees charts for a center cut out by any finite subset of polynomial coordinates. -/

open _root_.MvPolynomial

universe u

variable {σ R : Type u} [CommRing R] [DecidableEq σ]

def subsetCoordinateIdeal (C : Finset σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span (X '' (C : Set σ))

abbrev subsetCoordinateElement (C : Finset σ) (i : C) : subsetCoordinateIdeal (R := R) C :=
  ⟨X i.val, Ideal.subset_span ⟨i.val, i.property, rfl⟩⟩

abbrev subsetCoordinateBlowupChart (C : Finset σ) (i : C) :=
  Blowup.Charts.Construction.blowupChart (subsetCoordinateIdeal (R := R) C) (subsetCoordinateElement C i)

def subsetCoordinateSubstitution (C : Finset σ) (i : C) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom MvPolynomial.C (fun j => if j = i.val then X j else
    if j ∈ C then X i.val * X j else X j)

theorem subsetCoordinateSubstitution_C (C : Finset σ) (i : C) (r : R) :
    subsetCoordinateSubstitution C i (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [subsetCoordinateSubstitution]

theorem subsetCoordinateSubstitution_self (C : Finset σ) (i : C) :
    subsetCoordinateSubstitution (R := R) C i (X i.val) = X i.val := by
  simp [subsetCoordinateSubstitution]

theorem subsetCoordinateSubstitution_center (C : Finset σ) (i : C) (j : σ)
    (hji : j ≠ i.val) (hj : j ∈ C) :
    subsetCoordinateSubstitution (R := R) C i (X j) = X i.val * X j := by
  simp [subsetCoordinateSubstitution, hji, hj]

theorem subsetCoordinateSubstitution_outside (C : Finset σ) (i : C) (j : σ) (hj : j ∉ C) :
    subsetCoordinateSubstitution (R := R) C i (X j) = X j := by
  have hji : j ≠ i.val := fun h => hj (h.symm ▸ i.property)
  simp [subsetCoordinateSubstitution, hji, hj]

theorem subsetCoordinateSubstitution_ideal (C : Finset σ) (i : C) :
    (subsetCoordinateIdeal (R := R) C).map (subsetCoordinateSubstitution C i) =
      Ideal.span {X i.val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro p ⟨j, hj, rfl⟩
    change subsetCoordinateSubstitution C i (X j) ∈ Ideal.span {X i.val}
    by_cases hji : j = i.val
    · rw [hji, subsetCoordinateSubstitution_self]
      exact Ideal.mem_span_singleton_self _
    · rw [subsetCoordinateSubstitution_center C i j hji hj]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem, ← subsetCoordinateSubstitution_self (R := R) C i]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i.val, i.property, rfl⟩)

def subsetCoordinateBlowupToPolynomial (C : Finset σ) (i : C) :
    subsetCoordinateBlowupChart (R := R) C i →+* MvPolynomial σ R :=
  ChartLift.Construction.blowupChartLift (subsetCoordinateIdeal C) (subsetCoordinateElement C i)
    (subsetCoordinateSubstitution C i)
    (by simpa only [subsetCoordinateSubstitution_self] using subsetCoordinateSubstitution_ideal (R := R) C i)
    (by simpa only [subsetCoordinateSubstitution_self] using isRegular_X (R := R) (n := i.val))

theorem subsetCoordinateBlowupToPolynomial_constants (C : Finset σ) (i : C) (p : MvPolynomial σ R) :
    subsetCoordinateBlowupToPolynomial C i
      (Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) p) =
        subsetCoordinateSubstitution C i p := ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ p

def polynomialToSubsetCoordinateBlowup (C : Finset σ) (i : C) :
    MvPolynomial σ R →+* subsetCoordinateBlowupChart (R := R) C i :=
  eval₂Hom ((Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i)).comp MvPolynomial.C)
    (fun j => if j = i.val then
      Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (X j)
    else if hj : j ∈ C then
      ExceptionalIdeal.Construction.blowupChartRatio (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (subsetCoordinateElement C ⟨j, hj⟩)
    else Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (X j))

theorem polynomialToSubsetCoordinateBlowup_C (C : Finset σ) (i : C) (r : R) :
    polynomialToSubsetCoordinateBlowup C i (MvPolynomial.C r) =
      Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (MvPolynomial.C r) := by
  simp [polynomialToSubsetCoordinateBlowup]

theorem polynomialToSubsetCoordinateBlowup_self (C : Finset σ) (i : C) :
    polynomialToSubsetCoordinateBlowup (R := R) C i (X i.val) =
      Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (X i.val) := by
  simp [polynomialToSubsetCoordinateBlowup]

theorem polynomialToSubsetCoordinateBlowup_center (C : Finset σ) (i : C) (j : σ)
    (hji : j ≠ i.val) (hj : j ∈ C) :
    polynomialToSubsetCoordinateBlowup (R := R) C i (X j) =
      ExceptionalIdeal.Construction.blowupChartRatio (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (subsetCoordinateElement C ⟨j, hj⟩) := by
  simp [polynomialToSubsetCoordinateBlowup, hji, hj]

theorem polynomialToSubsetCoordinateBlowup_outside (C : Finset σ) (i : C) (j : σ) (hj : j ∉ C) :
    polynomialToSubsetCoordinateBlowup (R := R) C i (X j) =
      Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (X j) := by
  have hji : j ≠ i.val := fun h => hj (h.symm ▸ i.property)
  simp [polynomialToSubsetCoordinateBlowup, hji, hj]

theorem polynomialToSubsetCoordinateBlowup_substitution (C : Finset σ) (i : C) :
    (polynomialToSubsetCoordinateBlowup (R := R) C i).comp (subsetCoordinateSubstitution C i) =
      Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, subsetCoordinateSubstitution_C, polynomialToSubsetCoordinateBlowup_C]
  · intro j
    rw [RingHom.comp_apply]
    by_cases hji : j = i.val
    · rw [hji, subsetCoordinateSubstitution_self, polynomialToSubsetCoordinateBlowup_self]
    · by_cases hj : j ∈ C
      · rw [subsetCoordinateSubstitution_center C i j hji hj, map_mul,
          polynomialToSubsetCoordinateBlowup_self, polynomialToSubsetCoordinateBlowup_center C i j hji hj]
        exact ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (subsetCoordinateIdeal C) (subsetCoordinateElement C i)
          (subsetCoordinateElement C ⟨j, hj⟩)
      · rw [subsetCoordinateSubstitution_outside C i j hj, polynomialToSubsetCoordinateBlowup_outside C i j hj]

theorem subsetCoordinateBlowupToPolynomial_ratio (C : Finset σ) (i : C) (j : C) (hji : j.val ≠ i.val) :
    subsetCoordinateBlowupToPolynomial (R := R) C i
      (ExceptionalIdeal.Construction.blowupChartRatio (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (subsetCoordinateElement C j)) = X j.val := by
  apply (isRegular_X (R := R) (n := i.val)).left
  have h := congrArg (subsetCoordinateBlowupToPolynomial (R := R) C i)
    (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (subsetCoordinateIdeal C) (subsetCoordinateElement C i) (subsetCoordinateElement C j))
  simpa only [map_mul, subsetCoordinateBlowupToPolynomial_constants,
    subsetCoordinateSubstitution_self, subsetCoordinateSubstitution_center C i j.val hji j.property] using h

theorem subsetCoordinateBlowupToPolynomial_fromPolynomial (C : Finset σ) (i : C) :
    (subsetCoordinateBlowupToPolynomial (R := R) C i).comp (polynomialToSubsetCoordinateBlowup C i) =
      RingHom.id (MvPolynomial σ R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, polynomialToSubsetCoordinateBlowup_C,
      subsetCoordinateBlowupToPolynomial_constants, subsetCoordinateSubstitution_C]
    rfl
  · intro j
    rw [RingHom.comp_apply]
    by_cases hji : j = i.val
    · rw [hji, polynomialToSubsetCoordinateBlowup_self,
        subsetCoordinateBlowupToPolynomial_constants, subsetCoordinateSubstitution_self]
      rfl
    · by_cases hj : j ∈ C
      · rw [polynomialToSubsetCoordinateBlowup_center C i j hji hj,
          subsetCoordinateBlowupToPolynomial_ratio C i ⟨j, hj⟩ hji]
        rfl
      · rw [polynomialToSubsetCoordinateBlowup_outside C i j hj,
          subsetCoordinateBlowupToPolynomial_constants, subsetCoordinateSubstitution_outside C i j hj]
        rfl

theorem polynomialToSubsetCoordinateBlowup_toPolynomial (C : Finset σ) (i : C) :
    (polynomialToSubsetCoordinateBlowup (R := R) C i).comp (subsetCoordinateBlowupToPolynomial C i) =
      RingHom.id (subsetCoordinateBlowupChart (R := R) C i) := by
  apply ChartLift.Construction.blowupChart_hom_ext (subsetCoordinateIdeal (R := R) C) (subsetCoordinateElement C i)
    (Blowup.Charts.Construction.blowupChartConstants (subsetCoordinateIdeal C) (subsetCoordinateElement C i))
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular _ _)
  · intro p
    rw [RingHom.comp_apply, subsetCoordinateBlowupToPolynomial_constants]
    exact congrArg (fun f : MvPolynomial σ R →+* subsetCoordinateBlowupChart (R := R) C i => f p)
      (polynomialToSubsetCoordinateBlowup_substitution C i)
  · intro p
    rfl

/-- Every actual chart of a coordinate-subset blowup is again polynomial affine space. -/
def subsetCoordinateBlowupChartEquiv (C : Finset σ) (i : C) :
    subsetCoordinateBlowupChart (R := R) C i ≃+* MvPolynomial σ R :=
  RingEquiv.ofRingHom (subsetCoordinateBlowupToPolynomial C i) (polynomialToSubsetCoordinateBlowup C i)
    (subsetCoordinateBlowupToPolynomial_fromPolynomial C i) (polynomialToSubsetCoordinateBlowup_toPolynomial C i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction
