import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Positive Test Family -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! A restricted test family with nonnegative real values and a strictly
positive theta value. The archimedean factors are actual smooth bumps. -/

open scoped Classical _root_.NumberField
open _root_.NumberField Filter

namespace PositiveTestFamily.LocalAnalysis

theorem exists_positive_bruhat_of_field_model
    {k l : Type} [NormedField k] [NormedField l] [NormedAlgebra ℝ l] [FiniteDimensional ℝ l]
    (N : ℕ) (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N, f.val 0 = 1 ∧ ∀ x, (‖f.val x‖ : ℂ) = f.val x := by
  obtain ⟨g, -, hg, hd, hb, hzero⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : Local.FunctionsMetaplectic.Construction.Position l N)) (n := ⊤)
      (s := Set.univ) Filter.univ_mem
  have hs : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg.comp_left rfl
  let φ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd)
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi
  let f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨φ ∘ p,
    FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p (ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨φ, rfl⟩)⟩
  refine ⟨f, ?_, fun x => ?_⟩
  · change (g (p 0) : ℂ) = 1
    rw [map_zero, hzero, Complex.ofReal_one]
  · change (‖(g (p x) : ℂ)‖ : ℂ) = (g (p x) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb (Set.mem_range_self (p x))).1]

end PositiveTestFamily.LocalAnalysis

open OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveTestFamily.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem PositiveTestFamily.Construction.exists_positive_archimedean_bruhat (v : InfinitePlace F) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N,
      f.val 0 = 1 ∧ ∀ x, (‖f.val x‖ : ℂ) = f.val x := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact PositiveTestFamily.LocalAnalysis.exists_positive_bruhat_of_field_model N
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
  · exact PositiveTestFamily.LocalAnalysis.exists_positive_bruhat_of_field_model N
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous

theorem PositiveTestFamily.Construction.exists_positive_restricted_test_family :
    ∃ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N,
      (∀ v, (f v).val 0 = 1) ∧ ∀ v x, (‖(f v).val x‖ : ℂ) = (f v).val x := by
  choose φ hzero hpos using PositiveTestFamily.Construction.exists_positive_archimedean_bruhat F N
  let f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N :=
    { component := fun v => match v with
        | .inl w => φ w
        | .inr w => Vacuum.Construction.finiteVacuum F N w
      unramified := Eventually.of_forall (fun _ => rfl) }
  refine ⟨f, ?_, ?_⟩
  · intro v
    cases v with
    | inl v => exact hzero v
    | inr v => exact Vacuum.Construction.finiteVacuum_zero F N v
  · intro v x
    cases v with
    | inl v => exact hpos v x
    | inr v =>
        by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
        · change (‖(Vacuum.Construction.finiteVacuum F N v).val x‖ : ℂ) = (Vacuum.Construction.finiteVacuum F N v).val x
          rw [RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v x hx, norm_one, Complex.ofReal_one]
        · change (‖(Vacuum.Construction.finiteVacuum F N v).val x‖ : ℂ) = (Vacuum.Construction.finiteVacuum F N v).val x
          rw [FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v x hx, norm_zero, Complex.ofReal_zero]

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.value_nonnegative (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (hf : ∀ v x, (‖(f v).val x‖ : ℂ) = (f v).val x) (a : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    (‖f.value F N a‖ : ℂ) = f.value F N a := by
  have hp := (f.localValue_hasProd F N a).norm.map Complex.ofRealHom Complex.continuous_ofReal
  have hp' : HasProd (f.localValue F N a) (‖f.value F N a‖ : ℂ) := by
    apply hp.congr_fun
    intro v
    exact (hf v _).symm
  exact hp'.unique (f.localValue_hasProd F N a)

theorem PositiveTestFamily.Construction.exists_theta_nonzero : ∃ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N, f.theta F N ≠ 0 := by
  obtain ⟨f, hzero, hpos⟩ := PositiveTestFamily.Construction.exists_positive_restricted_test_family F N
  have hz : f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((0 : Fin N → F) i)) = 1 := by
    have hv (v : ArchimedeanAdeles.Construction.Places F) : f.localValue F N
        (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((0 : Fin N → F) i)) v = 1 := by
      change (f v).val (fun _ : Fin N => ArchimedeanAdeles.Construction.evaluate F v (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (0 : F))) = 1
      simp only [map_zero]
      exact hzero v
    change (∏' v, f.localValue F N _ v) = 1
    simp only [hv, tprod_one]
  have hnonneg (q : Fin N → F) :
      0 ≤ (f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))).re := by
    rw [← f.value_nonnegative F N hpos, Complex.ofReal_re]
    exact norm_nonneg _
  have hsum : Summable (fun q : Fin N → F =>
      (f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))).re) :=
    Complex.reCLM.summable (f.theta_summable F N)
  have hle := hsum.le_tsum 0 (fun q _ => hnonneg q)
  rw [hz, Complex.one_re] at hle
  have hreal : 1 ≤ (f.theta F N).re := by
    change 1 ≤ (∑' q : Fin N → F, f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))).re
    rw [Complex.re_tsum (f.theta_summable F N)]
    exact hle
  refine ⟨f, fun h => ?_⟩
  rw [h, Complex.zero_re] at hreal
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hreal

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
