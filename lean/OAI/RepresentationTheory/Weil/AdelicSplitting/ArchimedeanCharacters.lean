import OAI.RepresentationTheory.Weil.AdelicSplitting.TestSpace

/-! # Archimedean Characters -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters.LocalAnalysis

noncomputable section

section

/-! Smoothness and bounded derivatives of continuous unitary characters.
The proof first differentiates an interval primitive; it does not assume
a classification of characters or a differentiability hypothesis. -/

open _root_.MeasureTheory
open scoped ContDiff

theorem real_character_derivative
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) :
    ∃ c : ℂ, ∀ x : ℝ, HasDerivAt (fun t => ψ t) (c * ψ x) x := by
  let P : ℝ → ℂ := fun a => ∫ t in (0 : ℝ)..a, ψ t
  have hP (x : ℝ) : HasDerivAt P (ψ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hnonzero : ∃ a, P a ≠ 0 := by
    by_contra! h
    have he : P = fun _ => 0 := funext h
    have hd := hP 0
    rw [he] at hd
    have hh := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp at hh
  obtain ⟨a, ha⟩ := hnonzero
  have htranslate (x : ℝ) : P (x + a) - P x = ψ x * P a := by
    change (∫ t in (0 : ℝ)..(x + a), ψ t) - (∫ t in (0 : ℝ)..x, ψ t) = _
    rw [intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    calc
      (∫ t in x..x + a, ψ t) = ∫ t in (0 : ℝ)..a, ψ (x + t) := by
        rw [intervalIntegral.integral_comp_add_left]
        simp
      _ = ψ x * P a := by
        simp only [ψ.map_add_eq_mul]
        exact intervalIntegral.integral_const_mul _ _
  have hformula : (fun x => (P (x + a) - P x) / P a) = fun x => ψ x := by
    funext x
    rw [htranslate, mul_div_cancel_right₀ _ ha]
  refine ⟨(ψ a - 1) / P a, ?_⟩
  intro x
  have ht : HasDerivAt (fun t => P (t + a)) (ψ (x + a)) x := by
    simpa using! (hP (x + a)).scomp x ((hasDerivAt_id x).add_const a)
  have hd := (ht.sub (hP x)).mul_const (P a)⁻¹
  have hd' : HasDerivAt (fun t => (P (t + a) - P t) / P a)
      ((ψ (x + a) - ψ x) / P a) x := by
    simpa only [div_eq_mul_inv, Pi.sub_apply] using! hd
  rw [hformula] at hd'
  convert hd' using 1
  rw [ψ.map_add_eq_mul]
  ring

theorem real_character_temperate
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) :
    Function.HasTemperateGrowth (fun t => ψ t) := by
  obtain ⟨c, hd⟩ := real_character_derivative ψ hc
  have hderiv : deriv (fun t => ψ t) = fun t => c * ψ t := funext (fun t => (hd t).deriv)
  have hcd : ContDiff ℝ ∞ (fun t => ψ t) := by
    rw [contDiff_infty]
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr hc
    | succ n ih =>
        rw [Nat.cast_add, Nat.cast_one]
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
        rw [hderiv]
        exact contDiff_const.mul ih
  have hit (n : ℕ) : iteratedDeriv n (fun t => ψ t) = fun t => c ^ n * ψ t := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        rw [((hd t).const_mul (c ^ n)).deriv]
        rw [pow_succ, mul_assoc]
  refine ⟨hcd, fun n => ⟨0, ‖c‖ ^ n, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit]
  simp only [norm_mul, norm_pow, hu, mul_one, pow_zero, le_refl]

theorem complex_character_temperate
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) :
    Function.HasTemperateGrowth (fun z => ψ z) := by
  let r : ℝ →+ ℂ := Complex.ofRealHom.toAddMonoidHom
  let i : ℝ →+ ℂ :=
    { toFun := fun t => (t : ℂ) * Complex.I
      map_zero' := by simp
      map_add' := fun x y => by simp [add_mul] }
  let χr := ψ.compAddMonoidHom r
  let χi := ψ.compAddMonoidHom i
  have hr : Function.HasTemperateGrowth χr :=
    real_character_temperate χr (hc.comp Complex.continuous_ofReal) (fun t => hu _)
  have hi : Function.HasTemperateGrowth χi :=
    real_character_temperate χi (hc.comp (Complex.continuous_ofReal.mul continuous_const))
      (fun t => hu _)
  have he : (fun z => ψ z) = fun z : ℂ => χr z.re * χi z.im := by
    funext z
    change ψ z = ψ (z.re : ℂ) * ψ ((z.im : ℂ) * Complex.I)
    rw [← ψ.map_add_eq_mul, Complex.re_add_im]
  rw [he]
  exact (hr.comp Complex.reCLM.hasTemperateGrowth).mul
    (hi.comp Complex.imCLM.hasTemperateGrowth)

end

/-! Quadratic phases preserve the actual Bruhat space at archimedean
places, for arbitrary continuous unitary characters. -/

open scoped SchwartzMap ContDiff

theorem locallyConstant_contDiff_real {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : IsLocallyConstant f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_const.congr_of_eventuallyEq (hf.eventually_eq x)

theorem schwartzBruhat_archimedean_iff
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    {n : ℕ} {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} :
    f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ↔ ∃ φ : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position k n) ℂ, f = φ := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨d, e, φ, rfl⟩
        · exact ⟨hf.2.toSchwartzMap (locallyConstant_contDiff_real hf.1), rfl⟩
        · let a := e.symm.toAddEquiv.toRealLinearEquiv e.symm.continuous e.continuous
          exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ a φ, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
        obtain ⟨φ, rfl⟩ := hf
        obtain ⟨χ, rfl⟩ := hg
        exact ⟨φ + χ, rfl⟩
    | smul c f _ hf =>
        obtain ⟨φ, rfl⟩ := hf
        exact ⟨c • φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    let e := (Module.finBasis ℝ (Local.FunctionsMetaplectic.Construction.Position k n)).equivFunL
    let χ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm φ
    have h := Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem e.symm.toContinuousAddEquiv χ
    convert h using 1
    funext x
    change φ x = φ (e.symm (e x))
    rw [e.symm_apply_apply]

theorem quadratic_archimedean_temperate
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) : Function.HasTemperateGrowth (Local.FunctionsMetaplectic.Construction.quadratic B) := by
  have hc (i : Fin n) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position k n => x i) :=
    (ContinuousLinearMap.proj i : Local.FunctionsMetaplectic.Construction.Position k n →L[ℝ] k).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth
      (fun x : Local.FunctionsMetaplectic.Construction.Position k n => ∑ i, ∑ j, x i * B i j * x j) :=
    .sum (fun i _ => .sum (fun j _ => ((hc i).mul (.const (B i j))).mul (hc j)))
  convert! hq.mul (.const (2 : k)⁻¹) using 1
  funext x
  exact div_eq_mul_inv _ _

theorem quadraticOperator_archimedean_mem
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    {n : ℕ} (ψ : AddChar k ℂ) (hψ : Function.HasTemperateGrowth ψ)
    (B : Matrix (Fin n) (Fin n) k) {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨φ, rfl⟩ := schwartzBruhat_archimedean_iff.mp hf
  let χ := SchwartzMap.smulLeftCLM ℂ (fun x => ψ (Local.FunctionsMetaplectic.Construction.quadratic B x)) φ
  refine schwartzBruhat_archimedean_iff.mpr ⟨χ, ?_⟩
  funext x
  exact (SchwartzMap.smulLeftCLM_apply_apply
    (hψ.comp (quadratic_archimedean_temperate B)) φ x).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters.LocalAnalysis
