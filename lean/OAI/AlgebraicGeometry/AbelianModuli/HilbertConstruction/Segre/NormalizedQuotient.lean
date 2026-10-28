import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedCoordinates

/-! # Normalized Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedQuotient

noncomputable section

/-! The normalized rank-one matrix scheme is the affine product chart, over every ring. -/

open _root_.MvPolynomial

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w} (i : σ) (j : τ)

theorem segreNormalizedQuotient_pivot :
    Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (i, j)) = 1 := by
  have h : Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (i, j) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

theorem segreNormalizedQuotient_entry (a : σ) (b : τ) :
    Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (a, b)) =
      Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (a, j)) *
        Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (i, b)) := by
  have h : Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (NormalizedCoordinates.segreMinor R a i b j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨((a, b), (i, j)), rfl⟩))
  rw [NormalizedCoordinates.segreMinor, map_sub, map_mul, map_mul, segreNormalizedQuotient_pivot, mul_one] at h
  exact sub_eq_zero.mp h

def segreNormalizedChartInverse :
    NormalizedCoordinates.SegreChartRing R i j →ₐ[R] (MvPolynomial (σ × τ) R ⧸ NormalizedCoordinates.segreNormalizedIdeal R i j) :=
  aeval (Sum.elim
    (fun a => Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (a.val, j)))
    (fun b => Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (i, b.val))))

theorem segreNormalizedChartInverse_row (a : σ) :
    segreNormalizedChartInverse R i j (NormalizedCoordinates.segreRowCoordinate R i j a) =
      Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (a, j)) := by
  classical
  by_cases h : a = i
  · subst a
    simp [NormalizedCoordinates.segreRowCoordinate, segreNormalizedQuotient_pivot]
  · simp [NormalizedCoordinates.segreRowCoordinate, h, segreNormalizedChartInverse]

theorem segreNormalizedChartInverse_column (b : τ) :
    segreNormalizedChartInverse R i j (NormalizedCoordinates.segreColumnCoordinate R i j b) =
      Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X (i, b)) := by
  classical
  by_cases h : b = j
  · subst b
    simp [NormalizedCoordinates.segreColumnCoordinate, segreNormalizedQuotient_pivot]
  · simp [NormalizedCoordinates.segreColumnCoordinate, h, segreNormalizedChartInverse]

theorem segreNormalizedQuotientMap_mk (p : MvPolynomial (σ × τ) R) :
    NormalizedCoordinates.segreNormalizedQuotientMap R i j (Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) p) =
      NormalizedCoordinates.segreChartEvaluation R i j p := rfl

theorem segreNormalizedQuotientMap_inverse :
    (NormalizedCoordinates.segreNormalizedQuotientMap R i j).comp (segreNormalizedChartInverse R i j) =
      AlgHom.id R (NormalizedCoordinates.SegreChartRing R i j) := by
  classical
  apply MvPolynomial.algHom_ext
  intro k
  cases k with
  | inl a => simp [AlgHom.comp_apply, segreNormalizedChartInverse, segreNormalizedQuotientMap_mk,
      NormalizedCoordinates.segreChartEvaluation, NormalizedCoordinates.segreRowCoordinate, NormalizedCoordinates.segreColumnCoordinate, a.property]
  | inr b => simp [AlgHom.comp_apply, segreNormalizedChartInverse, segreNormalizedQuotientMap_mk,
      NormalizedCoordinates.segreChartEvaluation, NormalizedCoordinates.segreRowCoordinate, NormalizedCoordinates.segreColumnCoordinate, b.property]

theorem segreNormalizedChartInverse_quotientMap :
    (segreNormalizedChartInverse R i j).comp (NormalizedCoordinates.segreNormalizedQuotientMap R i j) =
      AlgHom.id R (MvPolynomial (σ × τ) R ⧸ NormalizedCoordinates.segreNormalizedIdeal R i j) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro q
  change segreNormalizedChartInverse R i j
    (NormalizedCoordinates.segreNormalizedQuotientMap R i j (Ideal.Quotient.mk (NormalizedCoordinates.segreNormalizedIdeal R i j) (X q))) = _
  rw [segreNormalizedQuotientMap_mk]
  rw [NormalizedCoordinates.segreChartEvaluation, aeval_X]
  rw [map_mul, segreNormalizedChartInverse_row, segreNormalizedChartInverse_column]
  exact (segreNormalizedQuotient_entry R i j q.1 q.2).symm

def segreNormalizedChartEquiv :
    (MvPolynomial (σ × τ) R ⧸ NormalizedCoordinates.segreNormalizedIdeal R i j) ≃ₐ[R] NormalizedCoordinates.SegreChartRing R i j :=
  AlgEquiv.ofAlgHom (NormalizedCoordinates.segreNormalizedQuotientMap R i j) (segreNormalizedChartInverse R i j)
    (segreNormalizedQuotientMap_inverse R i j) (segreNormalizedChartInverse_quotientMap R i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedQuotient
