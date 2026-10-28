import OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinatePartialFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadratic
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients

/-! # Real Weyl Coefficients -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients.Construction

noncomputable section

section

/-! The real Weyl matrix coefficient as a Schwartz partial Fourier transform. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

def weylKernelCoordinates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (V × V) ≃L[ℝ] (V × V) where
  toFun x := (x.2 - x.1, x.2)
  invFun x := (x.2 - x.1, x.2)
  left_inv x := by simp only [sub_sub_cancel]
  right_inv x := by simp only [sub_sub_cancel]
  map_add' x y := by
    apply Prod.ext
    · change x.2 + y.2 - (x.1 + y.1) = (x.2 - x.1) + (y.2 - y.1)
      abel
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · exact (smul_sub a x.2 x.1).symm
    · rfl
  continuous_toFun := (continuous_snd.sub continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_snd.sub continuous_fst).prodMk continuous_snd

def weylKernelSchwartz {d : ℕ} (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (weylKernelCoordinates (Local.FunctionsMetaplectic.Construction.Position ℝ d))
    (SchwartzTensor.Construction.schwartzTensor f (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap h))

theorem weylKernelSchwartz_apply {d : ℕ} (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ)
    (q x : Local.FunctionsMetaplectic.Construction.Position ℝ d) : weylKernelSchwartz f h (q, x) = f (x - q) * conj (h x) := rfl

def weylMidpointPhase {d : ℕ} (x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) : ℝ :=
  -(∑ i, x.2 i * x.1 i) / 2

theorem weylMidpointPhase_temperate (d : ℕ) :
    Function.HasTemperateGrowth (weylMidpointPhase (d := d)) := by
  have h₁ (i : Fin d) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d => x.1 i) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d) (Local.FunctionsMetaplectic.Construction.Position ℝ d))).hasTemperateGrowth
  have h₂ (i : Fin d) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d => x.2 i) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d) (Local.FunctionsMetaplectic.Construction.Position ℝ d))).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.sum (fun i _ => (h₂ i).mul (h₁ i))).neg.mul (.const (2 : ℝ)⁻¹)

theorem realCharacter_temperate (a : ℝ) :
    Function.HasTemperateGrowth (fun t : ℝ => RealFourier.Construction.realCharacter a t) := by
  apply RealCharacter.Construction.continuous_unitary_real_character_temperate
  · change Continuous (fun t : ℝ => (Real.fourierChar (a * t) : ℂ))
    fun_prop
  · intro t
    exact Circle.norm_coe _

theorem realCharacter_one_apply (x : ℝ) :
    RealFourier.Construction.realCharacter 1 x = (Real.fourierChar x : ℂ) := by
  change (Real.fourierChar (1 * x) : ℂ) = _
  rw [one_mul]

def weylFrequencyReflection (d : ℕ) :
    (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) ≃L[ℝ] (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) :=
  (ContinuousLinearEquiv.refl ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prodCongr
    (LinearIsometryEquiv.neg ℝ (E := Local.FunctionsMetaplectic.Construction.Position ℝ d)).toContinuousLinearEquiv

def realWeylSchwartzKernel {d : ℕ} (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => RealFourier.Construction.realCharacter 1 (weylMidpointPhase x))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (weylFrequencyReflection d)
      (CoordinatePartialFourier.Construction.coordinatePartialFourier (weylKernelSchwartz f h)))

theorem realWeylSchwartzKernel_apply {d : ℕ} (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ)
    (q p : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    realWeylSchwartzKernel f h (q, p) =
      ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, RealFourier.Construction.realCharacter 1 (∑ i, p i * (x i - q i / 2)) * f (x - q) * conj (h x) := by
  have hphase : Function.HasTemperateGrowth
      (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d => RealFourier.Construction.realCharacter 1 (weylMidpointPhase x)) :=
    (realCharacter_temperate 1).comp (weylMidpointPhase_temperate d)
  rw [realWeylSchwartzKernel, SchwartzMap.smulLeftCLM_apply_apply hphase]
  change RealFourier.Construction.realCharacter 1 (weylMidpointPhase (q, p)) * CoordinatePartialFourier.Construction.coordinatePartialFourier (weylKernelSchwartz f h) (q, -p) = _
  rw [CoordinatePartialFourier.Construction.coordinatePartialFourier_apply, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [weylKernelSchwartz_apply, ← realCharacter_one_apply]
    change RealFourier.Construction.realCharacter 1 (weylMidpointPhase (q, p)) *
      (RealFourier.Construction.realCharacter 1 (-(∑ i, x i * (-p) i)) * (f (x - q) * conj (h x))) = _
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    have hp : weylMidpointPhase (q, p) + -(∑ i, x i * (-p) i) = ∑ i, p i * (x i - q i / 2) := by
      simp only [weylMidpointPhase, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
        mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div]
      have hh : (∑ i, x i * p i) = ∑ i, p i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      rw [hh]
      ring
    rw [hp]
    exact (mul_assoc _ _ _).symm

end

/-! Actual real Weyl matrix coefficients are Schwartz functions. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

def realPhasePairCoordinates (d : ℕ) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) :=
  ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin d) (Fin d) (fun _ => ℝ)

def realWeylFrequencyCoordinates (d : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) :=
  (realPhasePairCoordinates d).trans
    ((ContinuousLinearEquiv.refl ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prodCongr
      (LinearEquiv.smulOfUnit (Units.mk0 a ha) : Local.FunctionsMetaplectic.Construction.Position ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d).toContinuousLinearEquiv)

def realWeylCoefficientSchwartz {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realWeylFrequencyCoordinates d a ha)
    (realWeylSchwartzKernel f h)

theorem realWeylCoefficientSchwartz_apply {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
    realWeylCoefficientSchwartz a ha f h v = WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume f h v := by
  change realWeylSchwartzKernel f h (FourierCovariance.Construction.phasePosition v, a • FourierCovariance.Construction.phaseMomentum v) = _
  rw [realWeylSchwartzKernel_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change RealFourier.Construction.realCharacter 1 (∑ i, (a • FourierCovariance.Construction.phaseMomentum v) i * (x i - FourierCovariance.Construction.phasePosition v i / 2)) *
      f (x - FourierCovariance.Construction.phasePosition v) * conj (h x) =
      RealFourier.Construction.realCharacter a (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) *
        f (fun i => x i - v (Sum.inl i)) * conj (h x)
    congr 2
    change (Real.fourierChar (1 * ∑ i, (a * v (Sum.inr i)) * (x i - v (Sum.inl i) / 2)) : ℂ) =
      (Real.fourierChar (a * ∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) : ℂ)
    rw [one_mul, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem exists_real_weyl_coefficient_schwartz {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) [μ.IsAddHaarMeasure]
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ∃ Φ : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ, ∀ v, Φ v = WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v := by
  obtain ⟨a, ha, rfl⟩ := RealFourier.Construction.continuous_nontrivial_real_character ψ hc hu hn
  let φ := (RealFourier.Construction.realSchwartzEquiv d).symm f
  let η := (RealFourier.Construction.realSchwartzEquiv d).symm h
  let r := Measure.addHaarScalarFactor μ (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  have hμ : μ = r • (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  refine ⟨(r : ℂ) • realWeylCoefficientSchwartz a ha φ η, fun v => ?_⟩
  change (r : ℂ) * realWeylCoefficientSchwartz a ha φ η v = _
  rw [realWeylCoefficientSchwartz_apply]
  change (r : ℂ) * (∫ x, Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) v φ x * conj (η x)) = _
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient, hμ, integral_smul_nnreal_measure]
  change (r : ℂ) * _ = (r : ℂ) * _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Local.FunctionsMetaplectic.Construction.heisenbergFunction, φ, η, RealFourier.Construction.realSchwartzEquiv_symm_apply]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients.Construction
