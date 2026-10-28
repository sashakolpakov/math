import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryCoefficientReduction

/-! # Center Boundary Containment -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryContainment.Construction

noncomputable section

/-! A nonempty coordinate center contained in a boundary intersection
must include all its boundary coordinates among its defining equations. -/

variable {R : Type*} [CommRing R]

theorem derivation_preserves_span_of_generators (D : Derivation ℤ R R) (s : Set R)
    (hD : ∀ x ∈ s, D x ∈ Ideal.span s) {p : R} (hp : p ∈ Ideal.span s) :
    D p ∈ Ideal.span s := by
  refine Submodule.span_induction hD ?_ ?_ ?_ hp
  · rw [map_zero]
    exact Ideal.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Ideal.add_mem _ hx hy
  · intro a x hx ih
    change D (a * x) ∈ Ideal.span s
    rw [D.leibniz]
    change a * D x + x * D a ∈ Ideal.span s
    exact Ideal.add_mem _ ((Ideal.span s).mul_mem_left a ih)
      ((Ideal.span s).mul_mem_right (D a) hx)

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Differentiating in a coordinate outside the center preserves its ideal. -/
theorem etale_outside_coordinate_derivation_preserves_center
    (C : Finset σ) (j : σ) (hj : j ∉ C) {p : S}
    (hp : p ∈ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C) :
    Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) j p ∈
      Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C := by
  have heq : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C =
      Ideal.span (Set.range (fun i : C => algebraMap (MvPolynomial σ K) S (MvPolynomial.X i.val))) :=
    CenterPermissibility.Construction.etaleSubsetCoordinateIdeal_eq_span (K := K) (S := S) C
  rw [heq] at hp ⊢
  apply derivation_preserves_span_of_generators _ _ _ hp
  rintro x ⟨i, rfl⟩
  have hji : j ≠ i.val := fun h => hj (h.symm ▸ i.property)
  rw [Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X, ite_eq_right hji]
  exact Ideal.zero_mem _

/-- No outside coordinate can vanish identically on a nonempty coordinate
center: its transverse derivative is one. -/
theorem etale_coordinate_mem_proper_center_iff
    (C : Finset σ) (hC : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ≠ ⊤) (j : σ) :
    algebraMap (MvPolynomial σ K) S (MvPolynomial.X j) ∈
      Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ↔ j ∈ C := by
  constructor
  · intro hj
    by_contra hjC
    have hD := etale_outside_coordinate_derivation_preserves_center C j hjC hj
    rw [Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X, ite_eq_left rfl] at hD
    exact hC (Ideal.eq_top_of_isUnit_mem _ hD isUnit_one)
  · intro hj
    exact (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) C ⟨j, hj⟩).property

/-- Ideal containment of a nonempty coordinate center in a selected
boundary intersection implies the required containment of index sets. -/
theorem etale_coordinate_ideal_le_proper_center_iff
    (B C : Finset σ) (hC : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ≠ ⊤) :
    Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B ≤
      Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ↔ B ⊆ C := by
  constructor
  · intro h j hj
    exact (etale_coordinate_mem_proper_center_iff C hC j).mp
      (h (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) B ⟨j, hj⟩).property)
  · intro h
    apply Ideal.map_mono
    apply Ideal.span_mono
    rintro p ⟨j, hj, rfl⟩
    exact ⟨j, h hj, rfl⟩

variable [CharZero K] [IsAlgClosed K] [Finite σ]

/-- A nonempty lifted coefficient center includes every selected old
boundary coordinate; this supplies the index condition for actual chart
transform formulas, rather than assuming it. -/
theorem boundaryAuxiliaryCoefficient_center_indices
    (B C : Finset σ) (h : σ) (hhC : h ∈ C)
    (hC : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ≠ ⊤) (J : Ideal S) (m : ℕ)
    (hcoef : Boundary.AuxiliaryCoefficientReduction.Construction.boundaryAuxiliaryCoefficientIdeal (K := K) B h J m ≤
      (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)})) ^
          (m + 1).factorial) : B ⊆ C :=
  (etale_coordinate_ideal_le_proper_center_iff B C hC).mp
    (Boundary.AuxiliaryCoefficientReduction.Construction.boundaryAuxiliaryCoefficient_center_lift B C h hhC J m hcoef).2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryContainment.Construction
