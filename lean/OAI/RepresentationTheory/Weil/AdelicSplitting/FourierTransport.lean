import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel
import OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport

/-! # Fourier Transport -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport.LocalAnalysis

noncomputable section

section

/-! Transport of Fourier integrals and the prescribed self-dual measure
through a continuous local-field isomorphism. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

variable {k l : Type} [NormedField k] [NormedField l]
  [LocallyCompactSpace k] [LocallyCompactSpace l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
  [SecondCountableTopology k] [SecondCountableTopology l]

def fieldContinuousAddEquiv (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) : k ≃ₜ+ l where
  __ := e.toAddEquiv
  continuous_toFun := he
  continuous_invFun := hi

omit [LocallyCompactSpace k] [LocallyCompactSpace l]
    [SecondCountableTopology k] [SecondCountableTopology l] in
theorem scalarFourier_fieldTransport
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ) (μ : Measure k) (f : k → ℂ) (x : k) :
    TensorFourier.LocalAnalysis.scalarFourier (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (μ.map e)
      (f ∘ e.symm) (e x) = TensorFourier.LocalAnalysis.scalarFourier ψ μ f x := by
  let a := (fieldContinuousAddEquiv e he hi).toHomeomorph.toMeasurableEquiv
  have h := integral_map_equiv (μ := μ) a
    (fun y => f (e.symm y) * (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (-(e x * y)))
  change TensorFourier.LocalAnalysis.scalarFourier _ _ _ _ = _ at h
  refine h.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change f (e.symm (e y)) * ψ (e.symm (-(e x * e y))) = f y * ψ (-(x * y))
    rw [map_neg, map_mul, e.symm_apply_apply, e.symm_apply_apply]

omit [LocallyCompactSpace k] [LocallyCompactSpace l]
    [SecondCountableTopology k] [SecondCountableTopology l] in
omit [BorelSpace k] in
theorem scalarFourier_nnreal_smul (ψ : AddChar k ℂ) (r : ℝ≥0)
    (μ : Measure k) (f : k → ℂ) (x : k) :
    TensorFourier.LocalAnalysis.scalarFourier ψ (r • μ) f x = (r : ℂ) * TensorFourier.LocalAnalysis.scalarFourier ψ μ f x := by
  rw [TensorFourier.LocalAnalysis.scalarFourier, integral_smul_nnreal_measure]
  rfl

omit [SecondCountableTopology k] in
theorem selfDualMeasure_fieldTransport
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ) (ν : Measure l) [ν.IsAddHaarMeasure]
    (hPl : ∀ S : Set l, IsCompact S →
      (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier (ψ.compAddMonoidHom e.symm.toAddMonoidHom) ν
        (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2 ∂ν) = ν.real S) :
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = ν := by
  let a := fieldContinuousAddEquiv e he hi
  let em := a.toHomeomorph.toMeasurableEquiv
  let μ : Measure k := Measure.addHaar
  let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  let r : ℝ≥0 := Measure.addHaarScalarFactor (μ.map a) ν
  have hr : 0 < r := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hm : μ.map a = r • ν := Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  let S : Set l := e.symm ⁻¹' (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k)
  have hS : IsCompact S := by
    exact a.toHomeomorph.symm.isCompact_preimage.mpr (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact
  have hSmeas : MeasurableSet S := hS.measurableSet
  have hpre : a ⁻¹' S = (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) := by
    ext x
    simp [a, S, fieldContinuousAddEquiv]
  have hmass : μ.real (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) = (r : ℝ) * ν.real S := by
    have h := congrArg (fun m : Measure l => m.real S) hm
    rw [measureReal_def, Measure.map_apply (show Measurable a from a.continuous.measurable) hSmeas, hpre,
      ← measureReal_def, measureReal_nnreal_smul_apply] at h
    exact h
  have hμpos : 0 < μ.real (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) := by
    apply ENNReal.toReal_pos
    · exact (Measure.measure_pos_of_nonempty_interior μ (Local.FunctionsMetaplectic.Construction.referenceCompact k).interior_nonempty).ne'
    · exact (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measure_ne_top
  have hνne : ν.real S ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmass
    exact hμpos.ne' hmass
  have hind : ((Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k).indicator (fun _ => (1 : ℂ))) ∘ e.symm =
      S.indicator (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : y ∈ S <;> simp [S, Set.mem_preimage] at hy ⊢ <;> simp [hy]
  have hFourier (x : k) : Local.FunctionsMetaplectic.Construction.referenceFourier k ψ x =
      (r : ℂ) * TensorFourier.LocalAnalysis.scalarFourier ψ' ν (S.indicator (fun _ => (1 : ℂ))) (e x) := by
    rw [Local.FunctionsMetaplectic.Construction.referenceFourier, ← ComplexFourier.LocalAnalysis.scalarFourier_indicator _ _ _ (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measurableSet]
    rw [← scalarFourier_fieldTransport e he hi ψ μ _ x, hind]
    change TensorFourier.LocalAnalysis.scalarFourier ψ' (μ.map a) _ _ = _
    rw [hm, scalarFourier_nnreal_smul]
  have hI : (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier ψ' ν (S.indicator (fun _ => (1 : ℂ))) (e x)‖ ^ 2 ∂μ) =
      (r : ℝ) * ν.real S := by
    have h := integral_map_equiv (μ := μ) em
      (fun y => ‖TensorFourier.LocalAnalysis.scalarFourier ψ' ν (S.indicator (fun _ => (1 : ℂ))) y‖ ^ 2)
    change (∫ y, ‖TensorFourier.LocalAnalysis.scalarFourier ψ' ν (S.indicator (fun _ => (1 : ℂ))) y‖ ^ 2 ∂μ.map a) = _ at h
    rw [hm, integral_smul_nnreal_measure, hPl S hS] at h
    exact h.symm
  have hscale : Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = (r : ℝ) ^ 2 := by
    unfold Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared
    simp_rw [hFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg, mul_pow]
    rw [integral_const_mul, hI]
    change (r ^ 2 * (r * ν.real S)) / μ.real (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) = (r : ℝ) ^ 2
    rw [hmass]
    field_simp
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, hscale, Real.sqrt_sq r.coe_nonneg, Measure.map_smul _ he.measurable.aemeasurable]
  change ENNReal.ofReal ((r : ℝ)⁻¹) • μ.map a = ν
  rw [hm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def,
    smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end

/-! Transport of Fourier stability and inversion on the actual Bruhat spaces. -/

open _root_.MeasureTheory

variable {k l : Type} [NormedField k] [NormedField l]
  [SecondCountableTopology k] [SecondCountableTopology l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]

omit [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    [SecondCountableTopology k] [SecondCountableTopology l] in
theorem dot_field_map (e : k ≃+* l) (n : ℕ) (x y : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.dot (fun i => e (x i)) (fun i => e (y i)) = e (Local.FunctionsMetaplectic.Construction.dot x y) := by
  simp only [Local.FunctionsMetaplectic.Construction.dot, map_sum, map_mul]

theorem fourierIntegral_fieldTransport (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hm : μ.map e = ν) (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
      (Measure.pi (fun _ : Fin n => ν)) (f ∘ (FieldTransport.LocalAnalysis.positionFieldEquiv n e he hi).symm)
      (FieldTransport.LocalAnalysis.positionFieldEquiv n e he hi x) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f x := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv n e he hi
  have hp : MeasurePreserving p (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) :=
    measurePreserving_pi _ _ (fun _ => ⟨he.measurable, hm⟩)
  have h := hp.integral_comp p.toHomeomorph.measurableEmbedding
    (fun y => f (p.symm y) * (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (-Local.FunctionsMetaplectic.Construction.dot (p x) y))
  refine h.symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [p.symm_apply_apply]
    change f y * ψ (e.symm (-Local.FunctionsMetaplectic.Construction.dot (fun i => e (x i)) (fun i => e (y i)))) =
      f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)
    rw [dot_field_map, map_neg, e.symm_apply_apply]

theorem fourier_fieldTransport_analysis (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hm : μ.map e = ν)
    (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat l n,
      Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
        (Measure.pi (fun _ : Fin n => ν)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat l n)
    (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat l n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (Measure.pi (fun _ : Fin n => ν))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
          (Measure.pi (fun _ : Fin n => ν)) f.val) x = f.val (-x)) :
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val) x = f.val (-x) := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv n e he hi
  let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  let T (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Local.FunctionsMetaplectic.Construction.schwartzBruhat l n :=
    ⟨f.val ∘ p.symm, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm f.property⟩
  have ht (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ' (Measure.pi (fun _ : Fin n => ν)) (T f).val =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val ∘ p.symm := by
    funext y
    have h := fourierIntegral_fieldTransport e he hi n ψ μ ν hm f.val (p.symm y)
    change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ' (Measure.pi (fun _ : Fin n => ν)) (T f).val (p (p.symm y)) = _ at h
    simpa only [p.apply_symm_apply] using! h
  have hs (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := by
    have h := FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p (hStable (T f))
    rw [ht] at h
    convert h using 1
    funext x
    exact (congrArg (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val)
      (p.symm_apply_apply x)).symm
  refine ⟨hs, fun f x => ?_⟩
  let g : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n :=
    ⟨Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val, hs f⟩
  have h := fourierIntegral_fieldTransport e he hi n ψ μ ν hm g.val x
  have hf : g.val ∘ p.symm = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ' (Measure.pi (fun _ : Fin n => ν)) (T f).val :=
    (ht f).symm
  rw [hf, hInv] at h
  have hpneg : (T f).val (-(p x)) = f.val (-x) := by
    change f.val (p.symm (-(p x))) = f.val (-x)
    rw [map_neg, p.symm_apply_apply]
  rw [hpneg] at h
  exact h.symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport.LocalAnalysis
