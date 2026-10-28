import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyCenterLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientTransform

/-! # Coefficient Family Interval -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval.Construction

noncomputable section

/-! Coefficient bounds retained through successive actual controlled transforms. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {ι : Type*}

theorem weightedCoordinateDerivativeFamilyIdeal_le_relative
    (D : Derivation k R R) (z : R) (p : ι → R) (b : ℕ) :
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤
      CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b := by
  unfold WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal CoefficientIdeal.Construction.relativeCoefficientIdeal WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal
  apply iSup_mono
  intro j
  apply pow_le_pow_left'
  apply Ideal.span_le.mpr
  rintro x ⟨t, rfl⟩
  exact Ideal.mem_map_of_mem _ (CoefficientIdeal.Construction.iterated_relative_derivation_mem_differential k D
    (Ideal.span (Set.range p)) (p t) (Ideal.subset_span ⟨t, rfl⟩) j.val)

variable {σ L : Type u} [Field L] [IsAlgClosed L] [Finite σ]

include σ L in
/-- Every coefficient ideal between the fixed normal family and the intrinsic
relative coefficients detects exactly the same closed-point order condition. -/
theorem relative_coefficient_family_interval_order [Algebra ℚ R]
    (D : Derivation k R R) (z : R) (hz : D z = 1) (p : ι → R) (b : ℕ)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hupp : C ≤ CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b)
    [Algebra (MvPolynomial σ L) (R ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ L) (R ⧸ Ideal.span {z})]
    (M : Ideal R) [M.IsMaximal] (hzM : z ∈ M) :
    Ideal.span (Set.range p) ≤ M ^ b ↔
      C ≤ M.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  constructor
  · intro hM
    exact hupp.trans (CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order k z _ M b hM)
  · intro hC
    exact (WeightedGeneratorFamily.Construction.closedPoint_span_order_iff_weighted_family (σ := σ) (K := L)
      D z hz p M hzM b).mpr (hlow.trans hC)

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Both coefficient bounds survive the actual transform. The generating family
keeps its index set, and the normal derivative is its actual blowup lift. -/
theorem relative_coefficient_family_interval_transform [IsNoetherianRing R] [Algebra ℚ R]
    (I : Ideal R) (a z : I) (D : Derivation k R R) (ha : D a.val = 0) (hz : D z.val = 1)
    (p : ι → R) (b : ℕ) (hp : Ideal.span (Set.range p) ≤ I ^ b)
    (C : Ideal (R ⧸ Ideal.span {z.val}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z.val p b ≤ C)
    (hupp : C ≤ CoefficientIdeal.Construction.relativeCoefficientIdeal k z.val (Ideal.span (Set.range p)) b) :
    let C' := (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial})
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal (DifferentialBlowup.Construction.blowupRelativeChartDerivation k I a D)
        (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p a b hp) b ≤ C' ∧
      C' ≤ CoefficientIdeal.Construction.relativeCoefficientIdeal k (ExceptionalIdeal.Construction.blowupChartRatio I a z)
        (Ideal.span (Set.range (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p a b hp))) b := by
  let : Algebra ℤ (Blowup.Charts.Construction.blowupChart I a) := Ring.toIntAlgebra (Blowup.Charts.Construction.blowupChart I a)
  dsimp only
  constructor
  · change WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a (D.restrictScalars ℤ))
      (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p a b hp) b ≤ _
    rw [← WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal_blowup_colon I a z (D.restrictScalars ℤ) ha hz p b hp]
    exact Submodule.colon_mono (Ideal.map_mono hlow) le_rfl
  · have hc := NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular I a z (D.restrictScalars ℤ) ha hz
    have h := (Submodule.colon_mono (Ideal.map_mono hupp) le_rfl).trans
      (CoefficientTransform.Construction.relativeCoefficientTransform_le_new_relative k I (Ideal.span (Set.range p)) a z b hp hc)
    rw [ControlledGeneratorFamily.Construction.blowupControlledTransform_eq_span_family I p a b hp] at h
    exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval.Construction
