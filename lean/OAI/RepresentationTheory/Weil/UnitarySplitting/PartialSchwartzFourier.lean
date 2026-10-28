import OAI.RepresentationTheory.Weil.UnitarySplitting.SchwartzTensor

/-! # Partial Schwartz Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier.Construction

noncomputable section

section

/-! Differentiating a partial Fourier integral preserves Schwartz amplitudes. -/

open scoped SchwartzMap InnerProductSpace RealInnerProductSpace

variable {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def partialFourierPositionProjection : (V × W) →L[ℝ] (V × W) :=
  (ContinuousLinearMap.inl ℝ V W).comp (ContinuousLinearMap.fst ℝ V W)

def partialFourierFrequency : (V × W) →L[ℝ] (V × W) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (V × W) W ℝ).flip (ContinuousLinearMap.snd ℝ V W)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ V W))

theorem partialFourierFrequency_apply (x y : V × W) :
    partialFourierFrequency x y = ⟪x.2, y.2⟫_ℝ := rfl

def partialFourierStep (f : SchwartzMap (V × W) Z) :
    SchwartzMap (V × W) ((V × W) →L[ℝ] Z) :=
  SchwartzMap.postcompCLM
    ((ContinuousLinearMap.compL ℝ (V × W) (V × W) Z).flip partialFourierPositionProjection)
    (SchwartzMap.fderivCLM ℝ (V × W) Z f) +
  (-(2 * Real.pi * Complex.I) : ℂ) • SchwartzMap.smulRightCLM ℝ Z partialFourierFrequency f

theorem partialFourierStep_apply (f : SchwartzMap (V × W) Z) (q : V) (y : W) (v : V × W) :
    partialFourierStep f (q, y) v = fderiv ℝ f (q, y) (v.1, 0) +
      (-(2 * Real.pi * Complex.I) : ℂ) • (⟪y, v.2⟫_ℝ • f (q, y)) := rfl

theorem partialFourier_integrand_hasFDerivAt (f : SchwartzMap (V × W) Z) (y : W) (x : V × W) :
    HasFDerivAt (fun z : V × W => (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • f (z.1, y))
      ((Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • partialFourierStep f (x.1, y)) x := by
  have hc := Real.hasFDerivAt_fourierChar_neg_bilinear_right
    (partialFourierFrequency (V := V) (W := W)) (0, y) x
  have hpos : HasFDerivAt (fun z : V × W => (z.1, y)) partialFourierPositionProjection x := by
    convert! ((ContinuousLinearMap.fst ℝ V W).hasFDerivAt (x := x)).prodMk (hasFDerivAt_const y x) using 1
  have hf := (f.hasFDerivAt (x.1, y)).comp x hpos
  convert! hc.smul hf using 1
  apply ContinuousLinearMap.ext
  intro v
  change (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) •
      (fderiv ℝ f (x.1, y) (v.1, 0) + (-(2 * Real.pi * Complex.I) : ℂ) • (⟪y, v.2⟫_ℝ • f (x.1, y))) =
    (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • fderiv ℝ f (x.1, y) (v.1, 0) +
      ((-2 * Real.pi * Complex.I * (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ)) * (⟪y, v.2⟫_ℝ : ℂ)) • f (x.1, y)
  rw [smul_add]
  congr 1
  rw [← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  ring

end

section

/-! Partial Fourier integrals and differentiation under their integrals. -/

open _root_.MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace RealInnerProductSpace _root_.Topology

variable {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable [MeasurableSpace W] [BorelSpace W]
variable [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def partialFourierFunction (f : SchwartzMap (V × W) Z) (x : V × W) : Z :=
  𝓕 (SchwartzTensor.Construction.schwartzSlice f x.1) x.2

theorem partialFourierFunction_integral (f : SchwartzMap (V × W) Z) (x : V × W) :
    partialFourierFunction f x =
      ∫ y : W, (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • f (x.1, y) := by
  change 𝓕 (SchwartzTensor.Construction.schwartzSlice f x.1) x.2 = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rfl

theorem partialFourierFunction_decay (f : SchwartzMap (V × W) Z) (k : ℕ) :
    ∃ C : ℝ, ∀ x : V × W, ‖x‖ ^ k * ‖partialFourierFunction f x‖ ≤ C :=
  SchwartzTensor.Construction.schwartzSliceOperator_decay (FourierTransform.fourierCLM ℝ (SchwartzMap W Z)) f k

theorem partialFourier_integrand_integrable (f : SchwartzMap (V × W) Z) (x : V × W) :
    Integrable (fun y : W => (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • f (x.1, y)) :=
  (Real.fourierIntegral_convergent_iff x.2).mpr (SchwartzTensor.Construction.schwartzSlice f x.1).integrable

theorem partialFourierFunction_hasFDerivAt_of_amplitude [CompleteSpace Z]
    (f : SchwartzMap (V × W) Z) (A : SchwartzMap (V × W) ((V × W) →L[ℝ] Z))
    (hA : ∀ y : W, ∀ x : V × W,
      HasFDerivAt (fun z : V × W => (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • f (z.1, y))
        ((Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • A (x.1, y)) x)
    (x : V × W) :
    HasFDerivAt (partialFourierFunction f)
      (partialFourierFunction (Z := (V × W) →L[ℝ] Z) A x) x := by
  obtain ⟨b, hb, hbound⟩ := SchwartzTensor.Construction.schwartzSlice_integrable_uniform_bound (volume : Measure W) A
  have hd : HasFDerivAt
      (fun z : V × W => ∫ y : W, (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • f (z.1, y))
      (∫ y : W, (Real.fourierChar (-⟪y, x.2⟫_ℝ) : ℂ) • A (x.1, y)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ) (bound := b)
      (F := fun z : V × W => fun y : W => (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • f (z.1, y))
      (F' := fun z : V × W => fun y : W => (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • A (z.1, y))
      (by simp)
    · exact Filter.Eventually.of_forall fun z => (partialFourier_integrand_integrable f z).aestronglyMeasurable
    · exact partialFourier_integrand_integrable f x
    · exact (partialFourier_integrand_integrable (Z := (V × W) →L[ℝ] Z) A x).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y z _ => by
        simpa only [norm_smul, Circle.norm_coe, one_mul] using hbound z.1 y
    · exact hb
    · exact Filter.Eventually.of_forall fun y z _ => hA y z
  have heq : partialFourierFunction f =
      fun z : V × W => ∫ y : W, (Real.fourierChar (-⟪y, z.2⟫_ℝ) : ℂ) • f (z.1, y) :=
    funext (partialFourierFunction_integral f)
  rw [heq, partialFourierFunction_integral (Z := (V × W) →L[ℝ] Z)]
  exact hd
theorem partialFourierFunction_hasFDerivAt [CompleteSpace Z]
    (f : SchwartzMap (V × W) Z) (x : V × W) :
    HasFDerivAt (partialFourierFunction f)
      (partialFourierFunction (Z := (V × W) →L[ℝ] Z) (partialFourierStep f) x) x :=
  partialFourierFunction_hasFDerivAt_of_amplitude f (partialFourierStep f)
    (partialFourier_integrand_hasFDerivAt f) x

theorem partialFourierFunction_fderiv [CompleteSpace Z] (f : SchwartzMap (V × W) Z) :
    fderiv ℝ (partialFourierFunction f) = partialFourierFunction (Z := (V × W) →L[ℝ] Z) (partialFourierStep f) :=
  funext fun x => (partialFourierFunction_hasFDerivAt f x).fderiv

end

section

/-! The partial Fourier transform preserves the full Schwartz space. -/

open scoped SchwartzMap ContDiff

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable [MeasurableSpace W] [BorelSpace W]

theorem partialFourierFunction_contDiff_nat (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
      (f : SchwartzMap (V × W) Z), ContDiff ℝ n (partialFourierFunction f) := by
  induction n with
  | zero =>
      intro Z _ _ _ f
      exact contDiff_zero.mpr (show Differentiable ℝ (partialFourierFunction f) from
        fun x => (partialFourierFunction_hasFDerivAt f x).differentiableAt).continuous
  | succ n ih =>
      intro Z _ _ _ f
      let A : SchwartzMap (V × W) ((V × W) →L[ℝ] Z) := partialFourierStep f
      have hA := ih (Z := (V × W) →L[ℝ] Z) A
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (partialFourierFunction_hasFDerivAt f x).differentiableAt, by simp, ?_⟩
      rw [partialFourierFunction_fderiv]
      exact hA

theorem partialFourierFunction_derivative_decay (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
      (f : SchwartzMap (V × W) Z) (k : ℕ),
      ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (partialFourierFunction f) x‖ ≤ C := by
  induction n with
  | zero =>
      intro Z _ _ _ f k
      simpa only [norm_iteratedFDeriv_zero] using partialFourierFunction_decay f k
  | succ n ih =>
      intro Z _ _ _ f k
      obtain ⟨C, hC⟩ := ih (Z := (V × W) →L[ℝ] Z) (partialFourierStep f) k
      refine ⟨C, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, partialFourierFunction_fderiv]
      exact hC x

def schwartzPartialFourier {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    (f : SchwartzMap (V × W) Z) : SchwartzMap (V × W) Z where
  toFun := partialFourierFunction f
  smooth' := contDiff_infty.mpr fun n => partialFourierFunction_contDiff_nat n f
  decay' k n := partialFourierFunction_derivative_decay n f k

theorem schwartzPartialFourier_apply {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    (f : SchwartzMap (V × W) Z) (x : V × W) :
    schwartzPartialFourier f x = partialFourierFunction f x := rfl

end

/-! Marginals of Schwartz functions for arbitrary finite-dimensional Haar measures. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable [MeasurableSpace W] [BorelSpace W]
variable [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

def schwartzMarginal (f : SchwartzMap (V × W) Z) : SchwartzMap V Z :=
  SchwartzTensor.Construction.schwartzSlice (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.prodComm ℝ W V) (schwartzPartialFourier f)) (0 : W)

theorem schwartzMarginal_apply (f : SchwartzMap (V × W) Z) (x : V) :
    schwartzMarginal f x = ∫ y : W, f (x, y) := by
  change partialFourierFunction f (x, 0) = _
  rw [partialFourierFunction_integral]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]

theorem exists_schwartz_marginal_haar
    {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsAddHaarMeasure]
    (f : SchwartzMap (V × U) Z) :
    ∃ θ : SchwartzMap V Z, ∀ x, θ x = ∫ y : U, f (x, y) ∂μ := by
  let r := Module.finrank ℝ U
  let e : U ≃L[ℝ] EuclideanSpace ℝ (Fin r) :=
    (Module.finBasis ℝ U).equivFun.toContinuousLinearEquiv.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℝ)).symm
  let ν : Measure (EuclideanSpace ℝ (Fin r)) := μ.map e
  let : ν.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let a := Measure.addHaarScalarFactor ν (volume : Measure (EuclideanSpace ℝ (Fin r)))
  have hν : ν = a • volume := Measure.isAddLeftInvariant_eq_smul_of_regular ν volume
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    ((ContinuousLinearEquiv.refl ℝ V).prodCongr e.symm) f
  refine ⟨(a : ℝ) • schwartzMarginal F, fun x => ?_⟩
  change (a : ℝ) • schwartzMarginal F x = _
  rw [schwartzMarginal_apply]
  have hm : (∫ y : U, f (x, y) ∂μ) = ∫ y, F (x, y) ∂ν := by
    change _ = ∫ y, f (x, e.symm y) ∂μ.map e.toHomeomorph
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change f (x, y) = f (x, e.symm (e y))
      rw [e.symm_apply_apply]
  rw [hm, hν, integral_smul_nnreal_measure]
  rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier.Construction
