import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd

/-! # Real Weyl Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylFourier.Construction

noncomputable section

section

/-! Schwartz Weyl superpositions are actual real Bruhat test functions. -/

open _root_.MeasureTheory
open scoped SchwartzMap

def realPhasePositionLinear (d : ℕ) : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d →L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)

def realWeylSynthesisCoordinates (d : ℕ) :
    (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ≃L[ℝ] (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) where
  toFun x := (x.2, x.1 - realPhasePositionLinear d x.2)
  invFun x := (x.2 + realPhasePositionLinear d x.1, x.1)
  left_inv x := by simp only [sub_add_cancel]
  right_inv x := by simp only [add_sub_cancel_right]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change x.1 + y.1 - realPhasePositionLinear d (x.2 + y.2) =
        (x.1 - realPhasePositionLinear d x.2) + (y.1 - realPhasePositionLinear d y.2)
      rw [map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · change a • x.1 - realPhasePositionLinear d (a • x.2) = a • (x.1 - realPhasePositionLinear d x.2)
      rw [map_smul, smul_sub]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def realWeylSynthesisPhase {d : ℕ} (x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : ℝ :=
  ∑ i, x.2 (Sum.inr i) * (x.1 i - x.2 (Sum.inl i) / 2)

theorem realWeylSynthesisPhase_temperate (d : ℕ) :
    Function.HasTemperateGrowth (realWeylSynthesisPhase (d := d)) := by
  have hx (i : Fin d) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d => x.1 i) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d) (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d))).hasTemperateGrowth
  have hv (i : Fin d ⊕ Fin d) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d => x.2 i) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ d) (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d))).hasTemperateGrowth
  exact Function.HasTemperateGrowth.sum fun i _ =>
    (hv (Sum.inr i)).mul ((hx i).sub ((hv (Sum.inl i)).mul (.const (2 : ℝ)⁻¹)))

def realWeylSynthesisKernel {d : ℕ} (ψ : AddChar ℝ ℂ)
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => ψ (realWeylSynthesisPhase x))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realWeylSynthesisCoordinates d) (SchwartzTensor.Construction.schwartzTensor a f))

theorem realWeylSynthesisKernel_apply {d : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ)
    (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
    realWeylSynthesisKernel ψ a f (x, v) = a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x := by
  have hphase : Function.HasTemperateGrowth
      (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d => ψ (realWeylSynthesisPhase x)) :=
    (RealCharacter.Construction.continuous_unitary_real_character_temperate ψ hc hu).comp (realWeylSynthesisPhase_temperate d)
  rw [realWeylSynthesisKernel, SchwartzMap.smulLeftCLM_apply_apply hphase]
  change ψ (realWeylSynthesisPhase (x, v)) * (a v * f (x - FourierCovariance.Construction.phasePosition v)) =
    a v * (ψ (realWeylSynthesisPhase (x, v)) * f (x - FourierCovariance.Construction.phasePosition v))
  exact mul_left_comm _ _ _

theorem exists_real_weyl_synthesis_schwartz {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    ∃ θ : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ, ∀ x, θ x = WeylSynthesisAdd.Construction.weylSynthesis ψ ν a f x := by
  obtain ⟨θ, hθ⟩ := PartialSchwartzFourier.Construction.exists_schwartz_marginal_haar ν (realWeylSynthesisKernel ψ a f)
  refine ⟨θ, fun x => ?_⟩
  rw [hθ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => realWeylSynthesisKernel_apply ψ hc hu a f x v

theorem weylSynthesis_mem_real {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    WeylSynthesisAdd.Construction.weylSynthesis ψ ν a f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d := by
  obtain ⟨θ, hθ⟩ := exists_real_weyl_synthesis_schwartz ψ hc hu ν a ((RealFourier.Construction.realSchwartzEquiv d).symm f)
  have heq : WeylSynthesisAdd.Construction.weylSynthesis ψ ν a f.val = θ := by
    funext x
    rw [hθ]
    unfold WeylSynthesisAdd.Construction.weylSynthesis
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      simp only [Local.FunctionsMetaplectic.Construction.heisenbergFunction, RealFourier.Construction.realSchwartzEquiv_symm_apply]
  rw [heq]
  exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (ContinuousAddEquiv.refl _) θ

end

section

/-! Fourier inversion in the form used by the real Weyl reconstruction. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

theorem realCharacter_one_conj (t : ℝ) :
    conj (RealFourier.Construction.realCharacter 1 t) = RealFourier.Construction.realCharacter 1 (-t) := by
  rw [RealWeylCoefficients.Construction.realCharacter_one_apply, RealWeylCoefficients.Construction.realCharacter_one_apply]
  rw [AddChar.map_neg_eq_inv]
  rw [Circle.coe_inv]
  exact (Complex.inv_eq_conj (Circle.norm_coe _)).symm

theorem coordinateFourier_conjugate_evaluation {d : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (∫ p : Local.FunctionsMetaplectic.Construction.Position ℝ d, conj (RealFourier.Construction.coordinateSchwartzFourier d f p) * RealFourier.Construction.realCharacter 1 (-Local.FunctionsMetaplectic.Construction.dot p x)) = conj (f x) := by
  have hh := congrArg conj (RealFourier.Construction.coordinateSchwartzFourier_square f (-x))
  rw [neg_neg, RealFourier.Construction.coordinateSchwartzFourier_apply] at hh
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral at hh
  rw [← integral_conj] at hh
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [map_mul, realCharacter_one_conj]
    congr 1
    congr 1
    simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem coordinateFourier_conjugate_scaled_evaluation {d : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (a : ℝ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (∫ p : Local.FunctionsMetaplectic.Construction.Position ℝ d, conj (RealFourier.Construction.coordinateSchwartzFourier d f ((-a) • p)) * RealFourier.Construction.realCharacter a (Local.FunctionsMetaplectic.Construction.dot p x)) =
      |a|⁻¹ ^ d * conj (f x) := by
  have hphase (p : Local.FunctionsMetaplectic.Construction.Position ℝ d) : RealFourier.Construction.realCharacter a (Local.FunctionsMetaplectic.Construction.dot p x) =
      RealFourier.Construction.realCharacter 1 (-Local.FunctionsMetaplectic.Construction.dot ((-a) • p) x) := by
    change (Real.fourierChar (a * Local.FunctionsMetaplectic.Construction.dot p x) : ℂ) = (Real.fourierChar (1 * -Local.FunctionsMetaplectic.Construction.dot ((-a) • p) x) : ℂ)
    rw [one_mul]
    congr 2
    simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, neg_neg,
      mul_assoc, Finset.mul_sum]
  simp_rw [hphase]
  have hi := Measure.integral_comp_smul (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
    (fun p => conj (RealFourier.Construction.coordinateSchwartzFourier d f p) * RealFourier.Construction.realCharacter 1 (-Local.FunctionsMetaplectic.Construction.dot p x)) (-a)
  rw [coordinateFourier_conjugate_evaluation] at hi
  simpa only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow, abs_neg, inv_pow,
    Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv] using hi

end

section

/-! Fourier formulas for each position fiber of a real Weyl coefficient. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

theorem realCharacter_conj (a t : ℝ) :
    conj (RealFourier.Construction.realCharacter a t) = RealFourier.Construction.realCharacter a (-t) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (show ‖RealFourier.Construction.realCharacter a t‖ = 1 from Circle.norm_coe _)).symm

theorem real_weyl_phase_split {d : ℕ} (q p x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (∑ i, p i * (x i - q i / 2)) = -Local.FunctionsMetaplectic.Construction.dot p q / 2 + Local.FunctionsMetaplectic.Construction.dot p x := by
  simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div, Local.FunctionsMetaplectic.Construction.dot]
  ring

theorem real_weyl_fourier_frequency {d : ℕ} (a : ℝ) (p x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    RealFourier.Construction.realCharacter 1 (-Local.FunctionsMetaplectic.Construction.dot ((-a) • p) x) = RealFourier.Construction.realCharacter a (Local.FunctionsMetaplectic.Construction.dot p x) := by
  change (Real.fourierChar (1 * -Local.FunctionsMetaplectic.Construction.dot ((-a) • p) x) : ℂ) = (Real.fourierChar (a * Local.FunctionsMetaplectic.Construction.dot p x) : ℂ)
  rw [one_mul]
  congr 2
  simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, neg_neg,
    mul_assoc, Finset.mul_sum]

theorem realWeyl_coefficient_fourier_fiber {d : ℕ} (a : ℝ)
    (u f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (q p : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim q p) =
      RealFourier.Construction.realCharacter a (-Local.FunctionsMetaplectic.Construction.dot p q / 2) *
        RealFourier.Construction.coordinateSchwartzFourier d (SchwartzTensor.Construction.schwartzSlice (RealWeylCoefficients.Construction.weylKernelSchwartz u f) q) ((-a) • p) := by
  rw [RealFourier.Construction.coordinateSchwartzFourier_apply]
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [SchwartzTensor.Construction.schwartzSlice_apply, RealWeylCoefficients.Construction.weylKernelSchwartz_apply, real_weyl_fourier_frequency]
    change RealFourier.Construction.realCharacter a (∑ i, p i * (x i - q i / 2)) * u (x - q) * conj (f x) = _
    rw [real_weyl_phase_split, AddChar.map_add_eq_mul]
    ring

theorem realWeyl_reconstruction_fiber {d : ℕ} (a : ℝ)
    (u f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (q x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (∫ p : Local.FunctionsMetaplectic.Construction.Position ℝ d, conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim q p)) *
      Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) (Sum.elim q p) u x) =
      (|a|⁻¹ ^ d : ℂ) * (conj (u (x - q)) * f x) * u (x - q) := by
  let φ := SchwartzTensor.Construction.schwartzSlice (RealWeylCoefficients.Construction.weylKernelSchwartz u f) q
  have heq (p : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
      conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim q p)) *
        Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) (Sum.elim q p) u x =
      (conj (RealFourier.Construction.coordinateSchwartzFourier d φ ((-a) • p)) * RealFourier.Construction.realCharacter a (Local.FunctionsMetaplectic.Construction.dot p x)) * u (x - q) := by
    rw [realWeyl_coefficient_fourier_fiber, map_mul, realCharacter_conj]
    change (RealFourier.Construction.realCharacter a (-(-Local.FunctionsMetaplectic.Construction.dot p q / 2)) * conj (RealFourier.Construction.coordinateSchwartzFourier d φ ((-a) • p))) *
      (RealFourier.Construction.realCharacter a (∑ i, p i * (x i - q i / 2)) * u (x - q)) = _
    rw [real_weyl_phase_split]
    have hc : RealFourier.Construction.realCharacter a (-(-Local.FunctionsMetaplectic.Construction.dot p q / 2)) * RealFourier.Construction.realCharacter a (-Local.FunctionsMetaplectic.Construction.dot p q / 2 + Local.FunctionsMetaplectic.Construction.dot p x) =
        RealFourier.Construction.realCharacter a (Local.FunctionsMetaplectic.Construction.dot p x) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    calc
      _ = (conj (RealFourier.Construction.coordinateSchwartzFourier d φ ((-a) • p)) *
        (RealFourier.Construction.realCharacter a (-(-Local.FunctionsMetaplectic.Construction.dot p q / 2)) * RealFourier.Construction.realCharacter a (-Local.FunctionsMetaplectic.Construction.dot p q / 2 + Local.FunctionsMetaplectic.Construction.dot p x))) * u (x - q) := by ring
      _ = _ := by rw [hc]
  simp_rw [heq]
  rw [integral_mul_const, coordinateFourier_conjugate_scaled_evaluation]
  change (|a|⁻¹ ^ d : ℂ) * conj (u (x - q) * conj (f x)) * u (x - q) = _
  rw [map_mul, starRingEnd_self_apply]

end

/-! Exact real Weyl reconstruction in position and momentum coordinates. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

theorem realCharacter_continuous (a : ℝ) : Continuous (fun t : ℝ => RealFourier.Construction.realCharacter a t) := by
  change Continuous (fun t : ℝ => (Real.fourierChar (a * t) : ℂ))
  fun_prop

theorem realCharacter_norm (a t : ℝ) : ‖RealFourier.Construction.realCharacter a t‖ = 1 := Circle.norm_coe _

theorem realWeyl_reconstruction_pair_integrable {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (u f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    Integrable (fun z : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d =>
      conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim z.1 z.2)) *
        Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) (Sum.elim z.1 z.2) u x)
      ((volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prod volume) := by
  let : ((volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prod (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  let A := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap (RealWeylCoefficients.Construction.realWeylCoefficientSchwartz a ha u f)
  let K := SchwartzTensor.Construction.schwartzSlice (realWeylSynthesisKernel (RealFourier.Construction.realCharacter a) A u) x
  let B := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (RealWeylCoefficients.Construction.realPhasePairCoordinates d).symm K
  have hb : Integrable B ((volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prod volume) := B.integrable
  convert hb using 1
  funext z
  change _ = realWeylSynthesisKernel (RealFourier.Construction.realCharacter a) A u (x, Sum.elim z.1 z.2)
  rw [realWeylSynthesisKernel_apply (RealFourier.Construction.realCharacter a) (realCharacter_continuous a) (realCharacter_norm a)]
  change _ = conj (RealWeylCoefficients.Construction.realWeylCoefficientSchwartz a ha u f (Sum.elim z.1 z.2)) * _
  rw [RealWeylCoefficients.Construction.realWeylCoefficientSchwartz_apply]

theorem realWeyl_reconstruction_pair {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (u f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (∫ z : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d,
      conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim z.1 z.2)) *
        Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) (Sum.elim z.1 z.2) u x
      ∂((volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prod volume)) =
      (|a|⁻¹ ^ d : ℂ) * (∫ y : Local.FunctionsMetaplectic.Construction.Position ℝ d, conj (u y) * u y) * f x := by
  rw [integral_prod _ (realWeyl_reconstruction_pair_integrable a ha u f x)]
  simp_rw [realWeyl_reconstruction_fiber]
  have heq (q : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
      (|a|⁻¹ ^ d : ℂ) * (conj (u (x - q)) * f x) * u (x - q) =
      (|a|⁻¹ ^ d : ℂ) * (conj (u (x - q)) * u (x - q)) * f x := by ring
  simp_rw [heq]
  rw [integral_mul_const, integral_const_mul]
  congr 2
  exact integral_sub_left_eq_self (fun q : Local.FunctionsMetaplectic.Construction.Position ℝ d => conj (u q) * u q) volume x

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylFourier.Construction
