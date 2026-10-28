import OAI.Analysis.HodgeTheory.Decomposition.Coordinate
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-! # Coordinate Lp -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp.Constructions

noncomputable section

section

/-! Actual Euclidean L² classes of supported chart coefficients, with the
same uniform bound established for the genuine manifold metric. -/

open scoped _root_.Manifold
open _root_.MeasureTheory

section L2

variable {A F : Type*} [MeasurableSpace A] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {μ : Measure A}

theorem memLp_toLp_norm_sq (u : A → F) (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hu.toLp u))]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u x)

end L2

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)

include he hK hKe

theorem supportedEuclideanCoefficients_memLp
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0) :
    MemLp (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val) 2 volume :=
  (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n a hK hKe ha).continuous.memLp_of_hasCompactSupport
    (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n a.val hK hKe ha)

def supportedCoordinatesLp
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0) :
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (supportedEuclideanCoefficients_memLp V e he n hK hKe a ha).toLp
    (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val)

theorem supportedCoordinatesLp_norm_sq
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0) :
    ‖supportedCoordinatesLp V e he n hK hKe a ha‖ ^ 2 =
      ∫ z, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z‖ ^ 2 :=
  memLp_toLp_norm_sq _ _

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem supportedCoordinatesLp_uniform_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ∀ ha : ∀ x, x ∉ K → a x = 0,
        c * ‖supportedCoordinatesLp V e he n hK hKe a ha‖ ^ 2 ≤
          ‖Form.Constructions.smoothToProjectiveL2 V n a‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := Coordinate.Constructions.projective_supported_coordinate_norm_bound V e he n hK hKe
  refine ⟨c, hc, fun a ha => ?_⟩
  rw [supportedCoordinatesLp_norm_sq, ← inner_self_eq_norm_sq (𝕜 := ℂ), Form.Constructions.smoothToProjectiveL2_inner]
  exact hbound a ha

end

/-! The reverse L² coordinate estimate for smooth forms supported in a fixed
compact chart subset. Together the two estimates give norm equivalence. -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projective_supported_coordinate_upper
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ∀ ha : ∀ x, x ∉ K → a x = 0,
        ‖Form.Constructions.smoothToProjectiveL2 V n a‖ ^ 2 ≤ C * ‖supportedCoordinatesLp V e he n hK hKe a ha‖ ^ 2 := by
  let L := MeasureVolume.Constructions.chartCoordinateForward V e '' K
  have hL : IsCompact L := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe
  have hLU : L ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro z ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  obtain ⟨C, hC, hbound⟩ := CoordinateEstimates.Constructions.projectiveWeightedFormOperator_uniform_upper V e he n hL hLU
  refine ⟨C, hC, fun a ha => ?_⟩
  let u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val
  have huc : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n a.val hK hKe ha
  have hu : ContDiff ℝ ∞ u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n a hK hKe ha
  have hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e n a.val hK hKe ha
  have hnc : HasCompactSupport (fun z => ‖u z‖ ^ 2) := huc.mono (by
    intro z hz hzero
    apply hz
    simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  have hni : Integrable (fun z => ‖u z‖ ^ 2) volume :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hnc
  have hwi : Integrable (fun z => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z)) volume :=
    LocalAdjointForm.Constructions.smooth_inner_test_integrable volume _ u (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).clm_apply hu.contDiffOn) hu huc hs
  rw [supportedCoordinatesLp_norm_sq, ← inner_self_eq_norm_sq (𝕜 := ℂ), Form.Constructions.smoothToProjectiveL2_inner]
  change (Form.Constructions.projectiveL2Pair V n a a).re ≤ _
  rw [Coordinate.Constructions.projective_supported_coordinate_energy V e he n a (fun x hx => ha x (fun h => hx (hKe h))),
    ← integral_const_mul]
  apply integral_mono hwi (hni.const_mul C)
  intro z
  by_cases hz : z ∈ L
  · have h := (le_abs_self (inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z))).trans
      (hbound z hz (u z) (u z))
    simpa only [pow_two, mul_assoc] using h
  · have hz0 : u z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz
        (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e n a.val hK hKe ha h))
    change inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z) ≤ C * ‖u z‖ ^ 2
    rw [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, inner_zero_right]

end

end OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp.Constructions
