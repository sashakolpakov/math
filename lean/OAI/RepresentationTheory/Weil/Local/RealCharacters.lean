import OAI.RepresentationTheory.Weil.Local.RealFourierLp
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # Real Characters -/

namespace OAI.RepresentationTheory.Weil.Local.RealCharacters.Construction

noncomputable section

section

/-! Classification of continuous real characters from their integral primitives. -/

open _root_.MeasureTheory

def characterPrimitive (ψ : AddChar ℝ ℂ) (t : ℝ) : ℂ := ∫ s in 0..t, ψ s

theorem characterPrimitive_hasDerivAt (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (t : ℝ) :
    HasDerivAt (characterPrimitive ψ) (ψ t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem characterPrimitive_ne_zero (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) : ∃ a : ℝ, characterPrimitive ψ a ≠ 0 := by
  by_contra! h
  have heq : characterPrimitive ψ = fun _ => (0 : ℂ) := funext h
  have hd := characterPrimitive_hasDerivAt ψ hc 0
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const 0 (0 : ℂ))
  exact one_ne_zero (ψ.map_zero_eq_one.symm.trans hz)

theorem characterPrimitive_shift (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (a t : ℝ) :
    characterPrimitive ψ (t + a) - characterPrimitive ψ t =
      ψ t * characterPrimitive ψ a := by
  rw [characterPrimitive, characterPrimitive,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_add_right (fun s => ψ s) t (a := 0) (b := a)
  rw [zero_add, add_comm a t] at h
  rw [← h]
  simp only [ψ.map_add_eq_mul, intervalIntegral.integral_mul_const, characterPrimitive]
  exact mul_comm _ _

theorem real_character_eq_exp (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) :
    ∃ z : ℂ, ∀ t : ℝ, ψ t = Complex.exp (z * t) := by
  obtain ⟨a, ha⟩ := characterPrimitive_ne_zero ψ hc
  let z : ℂ := (ψ a - 1) / characterPrimitive ψ a
  have hfun : (fun t => (characterPrimitive ψ (t + a) - characterPrimitive ψ t) /
      characterPrimitive ψ a) = fun t => ψ t := by
    funext t
    rw [characterPrimitive_shift ψ hc, mul_div_cancel_right₀ _ ha]
  have hd (t : ℝ) : HasDerivAt (fun s => ψ s) (ψ t * z) t := by
    have h := (((characterPrimitive_hasDerivAt ψ hc (t + a)).scomp t
      ((hasDerivAt_id t).add_const a)).sub (characterPrimitive_hasDerivAt ψ hc t)).mul_const
        (characterPrimitive ψ a)⁻¹
    simp only [one_smul, ← div_eq_mul_inv, Function.comp_def, Pi.sub_apply, id_eq] at h
    rw [hfun] at h
    convert! h using 1
    rw [ψ.map_add_eq_mul]
    dsimp [z]
    ring
  have hg (t : ℝ) : HasDerivAt
      (fun s : ℝ => ψ s * Complex.exp (-z * s)) 0 t := by
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-z * s))
        (Complex.exp (-z * t) * -z) t :=
      by simpa using (((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp
    have h := (hd t).mul he
    convert! h using 1
    ring
  refine ⟨z, fun t => ?_⟩
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
    (fun t => (hg t).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ψ.map_zero_eq_one, mul_one] at hconst
  have he : Complex.exp (-z * (t : ℂ)) * Complex.exp (z * t) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  calc
    ψ t = ψ t * (Complex.exp (-z * t) * Complex.exp (z * t)) := by rw [he, mul_one]
    _ = Complex.exp (z * t) := by rw [← mul_assoc, hconst, one_mul]

theorem continuous_unitary_real_character (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) :
    ∃ c : ℝ, ψ = Gaussian.Construction.realCharacter c := by
  obtain ⟨z, hz⟩ := real_character_eq_exp ψ hc
  have hre : z.re = 0 := by
    have h := hu 1
    rw [hz] at h
    simpa only [Complex.ofReal_one, mul_one, Complex.norm_exp, Real.exp_eq_one_iff] using h
  refine ⟨z.im / (2 * Real.pi), ?_⟩
  ext t
  rw [hz, Gaussian.Construction.realCharacter_apply]
  congr 1
  have hz' : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hr : 2 * Real.pi * (z.im / (2 * Real.pi)) * t = z.im * t := by
    field_simp
  rw [hr, Complex.ofReal_mul]
  conv_lhs => rw [hz']
  ring

theorem continuous_nontrivial_unitary_real_character (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) : ∃ c : ℝ, c ≠ 0 ∧ ψ = Gaussian.Construction.realCharacter c := by
  obtain ⟨c, hψ⟩ := continuous_unitary_real_character ψ hc hu
  refine ⟨c, ?_, hψ⟩
  rintro rfl
  obtain ⟨t, ht⟩ := hn
  apply ht
  rw [hψ, Gaussian.Construction.realCharacter_apply]
  simp

end

/-! Character multiplication preserves Bruhat functions in every real additive chart. -/

open scoped SchwartzMap ContDiff

theorem continuous_unitary_coordinate_character_temperate
    {r : ℕ} (ψ : AddChar (Fin r → ℝ) ℂ)
    (hψ : Continuous (fun x : Fin r → ℝ => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) : Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ x) := by
  classical
  have hsingle (i : Fin r) :
      Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ (Pi.single i (x i))) := by
    let φ : AddChar ℝ ℂ :=
      { toFun := fun t => ψ (Pi.single i t)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := by
          intro s t
          rw [Pi.single_add, ψ.map_add_eq_mul] }
    have hc : Continuous (fun t : ℝ => φ t) := by
      apply hψ.comp
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
        fun_prop
      · simpa [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    obtain ⟨c, hφ⟩ := continuous_unitary_real_character φ hc (fun t => hunit _)
    have ht : Function.HasTemperateGrowth (fun t => φ t) := by
      rw [hφ]
      exact RealTestSpace.Construction.realCharacter_temperate c
    exact ht.comp (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).hasTemperateGrowth
  have hsum (s : Finset (Fin r)) :
      Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ (∑ i ∈ s, Pi.single i (x i))) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, ψ.map_zero_eq_one]
        exact Function.HasTemperateGrowth.const 1
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi, ψ.map_add_eq_mul, Pi.mul_def] using (hsingle i).mul ih
  simpa only [Finset.univ_sum_single] using hsum Finset.univ

theorem locallyConstant_real_contDiff {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} (hf : IsLocallyConstant f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_const.congr_of_eventuallyEq (hf.eventually_eq x)

theorem schwartzBruhat_realChart_iff
    {F : Type} [NormedField F] {d r : ℕ}
    (e : (Fin r → ℝ) ≃ₜ+ FunctionsMetaplectic.Construction.Position F d) {f : FunctionsMetaplectic.Construction.Position F d → ℂ} :
    f ∈ FunctionsMetaplectic.Construction.schwartzBruhat F d ↔
      ∃ φ : SchwartzMap (Fin r → ℝ) ℂ, f = fun x => φ (e.symm x) := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨r', e', φ, rfl⟩
        · have hl : IsLocallyConstant (f ∘ e) := hf.1.comp_continuous e.continuous
          have hc : HasCompactSupport (f ∘ e) := hf.2.comp_homeomorph e.toHomeomorph
          refine ⟨hc.toSchwartzMap (locallyConstant_real_contDiff hl), ?_⟩
          funext x
          change f x = f (e (e.symm x))
          rw [e.apply_symm_apply]
        · let a := e.trans e'.symm
          let L := a.toAddEquiv.toRealLinearEquiv a.continuous a.symm.continuous
          refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ, ?_⟩
          funext x
          change φ (e'.symm x) = φ (e'.symm (e (e.symm x)))
          rw [e.apply_symm_apply]
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
        obtain ⟨φ, rfl⟩ := hf
        obtain ⟨χ, rfl⟩ := hg
        exact ⟨φ + χ, rfl⟩
    | smul c f _ hf =>
        obtain ⟨φ, rfl⟩ := hf
        exact ⟨c • φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact FunctionsMetaplectic.Construction.schwartz_coordinate_mem e φ

theorem realChart_character_mul_mem
    {F : Type} [NormedField F] {d r : ℕ}
    (e : (Fin r → ℝ) ≃ₜ+ FunctionsMetaplectic.Construction.Position F d)
    (χ : AddChar (FunctionsMetaplectic.Construction.Position F d) ℂ)
    (hχ : Continuous (fun x : FunctionsMetaplectic.Construction.Position F d => χ x))
    (hunit : ∀ x, ‖χ x‖ = 1)
    {f : FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (fun x => χ x * f x) ∈ FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  obtain ⟨φ, rfl⟩ := (schwartzBruhat_realChart_iff e).mp hf
  let η : AddChar (Fin r → ℝ) ℂ := χ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  have hη : Function.HasTemperateGrowth (fun x : Fin r → ℝ => η x) :=
    continuous_unitary_coordinate_character_temperate η (hχ.comp e.continuous) (fun x => hunit _)
  let θ := SchwartzMap.smulLeftCLM ℂ (fun x : Fin r → ℝ => η x) φ
  apply (schwartzBruhat_realChart_iff e).mpr
  refine ⟨θ, ?_⟩
  funext x
  change χ x * φ (e.symm x) =
    (SchwartzMap.smulLeftCLM ℂ (fun x : Fin r → ℝ => η x) φ) (e.symm x)
  rw [SchwartzMap.smulLeftCLM_apply_apply hη]
  change χ x * φ (e.symm x) = χ (e (e.symm x)) * φ (e.symm x)
  rw [e.apply_symm_apply]

end

end OAI.RepresentationTheory.Weil.Local.RealCharacters.Construction
