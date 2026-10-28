import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform

/-! # Hypersurface Coefficient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceCoefficientTransform.Construction

noncomputable section

/-! Differential coefficient families on the hypersurface and its actual blowup transform. -/

universe u

section Families

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Differential coefficients of a specified generating family, on `z = 0`. -/
def coordinateDerivativeFamilyIdeal (D : Derivation k A A) (z : A) (p : ι → A) (j : ℕ) :
    Ideal (A ⧸ Ideal.span {z}) :=
  Ideal.span (Set.range (fun t => Ideal.Quotient.mk (Ideal.span {z}) (D^[j] (p t))))

/-- Coefficients of the generators suffice to test the order of their ideal. -/
theorem span_order_iff_coordinateDerivativeFamilyIdeals [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1) (p : ι → A)
    (M : Ideal A) (hzM : z ∈ M) (b : ℕ) :
    Ideal.span (Set.range p) ≤ M ^ b ↔ ∀ j < b,
      coordinateDerivativeFamilyIdeal D z p j ≤
        M.map (Ideal.Quotient.mk (Ideal.span {z})) ^ (b - j) := by
  constructor
  · intro h j hj
    apply Ideal.span_le.mpr
    rintro x ⟨t, rfl⟩
    exact (DifferentialCoefficientOrder.Construction.mem_pow_iff_coordinate_quotient_derivatives D z hz M hzM b (p t)).mp
      (h (Ideal.subset_span ⟨t, rfl⟩)) j hj
  · intro h
    apply Ideal.span_le.mpr
    rintro x ⟨t, rfl⟩
    apply (DifferentialCoefficientOrder.Construction.mem_pow_iff_coordinate_quotient_derivatives D z hz M hzM b (p t)).mpr
    intro j hj
    exact h j hj (Ideal.subset_span ⟨t, rfl⟩)

end Families

variable {R : Type u} [CommRing R]

/-- The actual morphism on hypersurface quotient rings induced by a blowup
chart and the divided hypersurface equation. -/
def blowupHypersurfaceChartMap (I : Ideal R) (a z : I) :
    (R ⧸ Ideal.span {z.val}) →+*
      (Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})).comp (Blowup.Charts.Construction.blowupChartConstants I a))
    (by
      intro r hr
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change Blowup.Charts.Construction.blowupChartConstants I a r ∈ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}
      rw [hs, map_mul, ← ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z]
      exact (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}).mul_mem_right _
        ((Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}).mul_mem_left _ (Ideal.mem_span_singleton_self _)))

theorem blowupHypersurfaceChartMap_mk (I : Ideal R) (a z : I) (r : R) :
    blowupHypersurfaceChartMap I a z (Ideal.Quotient.mk (Ideal.span {z.val}) r) =
      Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) (Blowup.Charts.Construction.blowupChartConstants I a r) := rfl

/-- The coefficient families have the exact exceptional factor predicted
by their derivative order, on the actual hypersurface quotient map. -/
theorem differentialCoefficientIdeal_blowup_factorization (I J : Ideal R) (a z : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (b j : ℕ) (hj : j ≤ b) (hJ : J ≤ I ^ b) :
    (DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j).map (blowupHypersurfaceChartMap I a z) =
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j)} *
      coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z)
        (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ) j := by
  rw [DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal, Ideal.map_span, ← Set.range_comp]
  have he : (blowupHypersurfaceChartMap I a z ∘
      fun p : J => Ideal.Quotient.mk (Ideal.span {z.val}) (D^[j] p.val)) =
      fun p : J =>
        (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^
            (b - j) *
          Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
            ((ChartDerivation.Construction.blowupChartDerivation I a D)^[j] (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ p)) := by
    funext p
    rw [Function.comp_apply, blowupHypersurfaceChartMap_mk]
    have hd := Coordinate.BlowupTransform.Construction.blowupChart_iteratedCoordinateDerivation_division I a D ha (b - j) j p.val
      (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ p)
      (by simpa only [Nat.sub_add_cancel hj] using Coordinate.BlowupTransform.Construction.blowupChartTransformSection_spec I J a b hJ p)
    rw [hd, map_mul,
      map_pow (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))]
  rw [he, ResidualCoefficientTransform.Construction.span_range_mul_left]
  rfl

/-- If the exceptional parameter remains regular on the hypersurface,
taking the coefficient ideal quotient gives precisely the divided family. -/
theorem differentialCoefficientIdeal_blowup_colon (I J : Ideal R) (a z : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (b j : ℕ) (hj : j ≤ b) (hJ : J ≤ I ^ b)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    ((DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j).map (blowupHypersurfaceChartMap I a z)).colon
        (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
          (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j)}) =
      coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z)
        (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ) j := by
  rw [differentialCoefficientIdeal_blowup_factorization I J a z D ha b j hj hJ,
    ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (hc.pow (b - j))]

variable [Algebra ℚ R]

local instance (I : Ideal R) (a : I) : Algebra ℚ (Blowup.Charts.Construction.blowupChart I a) :=
  ((Blowup.Charts.Construction.blowupChartConstants I a).comp (algebraMap ℚ R)).toAlgebra

/-- On a coordinate chart, the order of the actual controlled transform
is detected by the divided differential coefficient family. -/
theorem blowupControlledTransform_order_iff_coordinate_coefficients
    (I J : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (b : ℕ) (hJ : J ≤ I ^ b)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) (hzM : ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M) :
    ControlledTransform.Construction.blowupControlledTransform I J b a ≤ M ^ b ↔ ∀ j < b,
      coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z)
        (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ) j ≤
      M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) ^ (b - j) := by
  rw [Coordinate.BlowupTransform.Construction.blowupControlledTransform_eq_span_divisions I J a b hJ]
  exact span_order_iff_coordinateDerivativeFamilyIdeals (ChartDerivation.Construction.blowupChartDerivation I a D) _
    (Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate I a z D ha hz) _ M hzM b

/-- A persistent differential coordinate contains the entire transformed
high-order locus, which is then exactly detected by its coefficient families. -/
theorem blowupControlledTransform_order_locus_iff_coordinate_coefficients
    (I J : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (k : ℕ) (hJ : J ≤ I ^ (k + 1))
    (hzJ : z.val ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J k) (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    ControlledTransform.Construction.blowupControlledTransform I J (k + 1) a ≤ M ^ (k + 1) ↔
      ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M ∧ ∀ j < k + 1,
        coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z)
          (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a (k + 1) hJ) j ≤
        M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) ^ (k + 1 - j) := by
  constructor
  · intro hM
    have hzM : ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M := by
      have h := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow M (ControlledTransform.Construction.blowupControlledTransform I J (k + 1) a) 1 k
        (by simpa only [Nat.add_comm 1 k] using hM)
      have hz' := h (DifferentialIdealTransform.Construction.blowupChart_differential_hypersurface_persists I J a z k hJ hzJ)
      simpa only [pow_one] using hz'
    exact ⟨hzM, (blowupControlledTransform_order_iff_coordinate_coefficients I J a z D ha hz
      (k + 1) hJ M hzM).mp hM⟩
  · rintro ⟨hzM, hc⟩
    exact (blowupControlledTransform_order_iff_coordinate_coefficients I J a z D ha hz
      (k + 1) hJ M hzM).mpr hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceCoefficientTransform.Construction
