import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealChartTestSpace
import OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance

/-! # Real Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourier.Construction

noncomputable section

/-! Fourier inversion and a unitary Fourier operator at real places. -/

open _root_.MeasureTheory
open scoped FourierTransform SchwartzMap

def realCharacter (c : ℝ) : AddChar ℝ ℂ :=
  Circle.coeHom.compAddChar (Real.fourierChar.mulShift c)

theorem realCharacter_apply (c t : ℝ) :
    realCharacter c t = Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * Complex.I) := by
  change Complex.exp (((2 * Real.pi * (c * t) : ℝ) : ℂ) * Complex.I) = _
  rw [mul_assoc (2 * Real.pi) c t]

def euclideanSchwartzEquiv (n : ℕ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ where
  toFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f
  invFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm f
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

def coordinateSchwartzFourier (n : ℕ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ :=
  (euclideanSchwartzEquiv n).trans
    ((FourierTransform.fourierEquiv ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)).trans
      (euclideanSchwartzEquiv n).symm)

theorem coordinateSchwartzFourier_apply {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n f x = Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f x := by
  change 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f :
      SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)) (WithLp.toLp 2 x) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, realCharacter,
      MonoidHom.compAddChar_apply, Function.comp_apply, AddChar.mulShift_apply, one_mul]
    change (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) * f y =
      f y * (Real.fourierChar (-(∑ i, x i * y i)) : ℂ)
    exact mul_comm _ _

theorem coordinateSchwartzFourier_symm_apply {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (coordinateSchwartzFourier n).symm f x = coordinateSchwartzFourier n f (-x) := by
  change 𝓕⁻ (euclideanSchwartzEquiv n f) (WithLp.toLp 2 x) =
    𝓕 (euclideanSchwartzEquiv n f) (WithLp.toLp 2 (-x))
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
  rfl

theorem coordinateSchwartzFourier_square {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n (coordinateSchwartzFourier n f) x = f (-x) := by
  have h := congrArg (fun g : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ => g (-x))
    ((coordinateSchwartzFourier n).symm_apply_apply f)
  rw [coordinateSchwartzFourier_symm_apply, neg_neg] at h
  exact h

theorem coordinateSchwartzFourier_integral_norm_sq {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) :
    (∫ x, ‖coordinateSchwartzFourier n f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  have h := SchwartzMap.integral_norm_sq_fourier (euclideanSchwartzEquiv n f)
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding,
    ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding] at h
  exact h

def realSchwartzToBruhat {d : ℕ} :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d where
  toFun f := ⟨f, Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (ContinuousAddEquiv.refl _) f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realSchwartzToBruhat_bijective {d : ℕ} : Function.Bijective (realSchwartzToBruhat (d := d)) := by
  constructor
  · intro f g h
    exact DFunLike.ext' (congrArg Subtype.val h)
  · intro f
    obtain ⟨φ, hφ⟩ := (RealChartTestSpace.Construction.schwartzBruhat_realChart_iff (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ d))).mp f.property
    exact ⟨φ, Subtype.ext hφ.symm⟩

def realSchwartzEquiv (d : ℕ) : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d :=
  LinearEquiv.ofBijective realSchwartzToBruhat realSchwartzToBruhat_bijective

theorem realSchwartzEquiv_symm_apply {d : ℕ} (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (realSchwartzEquiv d).symm f x = f.val x :=
  congrArg (fun g : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d => g.val x) ((realSchwartzEquiv d).apply_symm_apply f)

def realBruhatFourier (d : ℕ) : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d :=
  (realSchwartzEquiv d).symm.trans ((coordinateSchwartzFourier d).trans (realSchwartzEquiv d))

theorem realBruhatFourier_apply {d : ℕ} (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (realBruhatFourier d f).val x = Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f.val x := by
  change coordinateSchwartzFourier d ((realSchwartzEquiv d).symm f) x = _
  rw [coordinateSchwartzFourier_apply]
  have hf : ((realSchwartzEquiv d).symm f : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) = f.val :=
    funext (realSchwartzEquiv_symm_apply f)
  rw [hf]

theorem realBruhatFourier_unitary {d : ℕ} (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (realBruhatFourier d f) = Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  let μ := Weak.Construction.referencePositionMeasure ℝ d
  have hm := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  change (∫ x, ‖(realBruhatFourier d f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ
  rw [hm, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  have hh := coordinateSchwartzFourier_integral_norm_sq ((realSchwartzEquiv d).symm f)
  simp_rw [coordinateSchwartzFourier_apply, realSchwartzEquiv_symm_apply] at hh
  have hf : ((realSchwartzEquiv d).symm f : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) = f.val :=
    funext (realSchwartzEquiv_symm_apply f)
  rw [hf] at hh
  simpa only [realBruhatFourier_apply] using hh

theorem continuous_nontrivial_real_character (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) : ∃ c : ℝ, c ≠ 0 ∧ ψ = realCharacter c := by
  obtain ⟨z, hz⟩ := RealCharacter.Construction.continuous_real_character_exponential ψ hc
  have hre : z.re = 0 := by
    have hh := hu 1
    rw [hz] at hh
    simpa only [Complex.ofReal_one, one_mul, Complex.norm_exp, Real.exp_eq_one_iff] using hh
  have hchar : ψ = realCharacter (z.im / (2 * Real.pi)) := by
    ext t
    rw [hz, realCharacter_apply]
    congr 1
    have hz' : z = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    have hr : 2 * Real.pi * (z.im / (2 * Real.pi)) * t = z.im * t := by field_simp
    rw [hr, Complex.ofReal_mul]
    conv_lhs => rw [hz']
    ring
  refine ⟨z.im / (2 * Real.pi), ?_, hchar⟩
  intro hzero
  obtain ⟨t, ht⟩ := hn
  apply ht
  rw [hchar, hzero, realCharacter_apply]
  simp

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourier.Construction
