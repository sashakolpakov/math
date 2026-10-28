import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator
import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis

/-! # Weak -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Weak.Construction

noncomputable section

section

/-! The concrete test space embeds faithfully in L². This connects the
energy-observation topology to ordinary norm topology, without assuming
any realization or splitting theorem. -/

open _root_.MeasureTheory
open scoped ENNReal

variable (F : Type) [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

abbrev referencePositionMeasure (d : ℕ) : Measure (Local.FunctionsMetaplectic.Construction.Position F d) :=
  Measure.pi (fun _ : Fin d => (Measure.addHaar : Measure F))

theorem test_memLp_two (d : ℕ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    MemLp f.val 2 (referencePositionMeasure F d) :=
  TestSpaceAnalysis.Construction.schwartzBruhat_memLp _ 2 f.property

def testToL2 (d : ℕ) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ]
    Lp ℂ 2 (referencePositionMeasure F d) where
  toFun f := (test_memLp_two F d f).toLp f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem testToL2_injective (d : ℕ) : Function.Injective (testToL2 F d) := by
  intro f g h
  apply Subtype.ext
  have hae : f.val =ᵐ[referencePositionMeasure F d] g.val :=
    (MemLp.toLp_eq_toLp_iff (test_memLp_two F d f) (test_memLp_two F d g)).mp h
  exact MeasureTheory.Measure.eq_of_ae_eq hae
    (TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property) (TestSpaceAnalysis.Construction.schwartzBruhat_continuous g.property)

theorem testToL2_norm (d : ℕ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ‖testToL2 F d f‖ = Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F d f) := by
  change ‖(test_memLp_two F d f).toLp f.val‖ = _
  rw [Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (test_memLp_two F d f)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div (2 : ℝ), ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rfl

theorem l2Energy_eq_zero_iff (d : ℕ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply testToL2_injective F d
    rw [map_zero, ← norm_eq_zero, testToL2_norm, h, Real.sqrt_zero]
  · rintro rfl
    simp [Local.FunctionsMetaplectic.Construction.l2Energy]

variable {F}

theorem circleScalar_continuous
    {E : Type} [NormedField E] [Algebra F E]
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    Continuous (Oscillator.Construction.circleScalar σ H K c ψ) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_const
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      change Continuous (fun z : Circle =>
        Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) ((z : ℂ) • p.1 - p.2)))
      simp_rw [← testToL2_norm, map_sub, map_smul]
      fun_prop
    · apply continuous_pi
      intro p
      change Continuous (fun z : Circle =>
        Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) ((↑(z⁻¹) : ℂ) • p.1 - p.2)))
      simp_rw [← testToL2_norm, map_sub, map_smul]
      fun_prop

omit [SecondCountableTopology F] in
theorem circleScalar_injective_of_test
    {E : Type} [NormedField E] [Algebra F E]
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) (hf : f ≠ 0) :
    Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) := by
  obtain ⟨x, hx⟩ : ∃ x, f.val x ≠ 0 := by
    by_contra! h
    apply hf
    apply Subtype.ext
    exact funext h
  intro z w h
  apply Circle.coe_injective
  have hh := congrArg (fun a : Oscillator.Construction.CircleExtension σ H K c ψ =>
    (Oscillator.Construction.oscillatorRepresentation σ H K c ψ a f).val x) h
  change (z : ℂ) * f.val x = (w : ℂ) * f.val x at hh
  exact mul_right_cancel₀ hx hh

end

section

/-! Energy-preserving operators preserve the genuine L² inner product. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem inner_eq_of_linear_norm_eq
    {S V : Type} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (L M : S →ₗ[ℂ] V) (h : ∀ f, ‖L f‖ = ‖M f‖) (f g : S) :
    ⟪L f, L g⟫_ℂ = ⟪M f, M g⟫_ℂ := by
  simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, h]

variable (F : Type) [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable (d : ℕ)

theorem testToL2_inner (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪testToL2 F d f, testToL2 F d g⟫_ℂ =
      ∫ x, g.val x * conj (f.val x) ∂ referencePositionMeasure F d := by
  change (∫ x, ⟪(testToL2 F d f) x, (testToL2 F d g) x⟫_ℂ
    ∂ referencePositionMeasure F d) = _
  apply integral_congr_ae
  filter_upwards [(test_memLp_two F d f).coeFn_toLp,
    (test_memLp_two F d g).coeFn_toLp] with x hf hg
  change (testToL2 F d f) x = f.val x at hf
  change (testToL2 F d g) x = g.val x at hg
  rw [hf, hg]
  simp only [RCLike.inner_apply]

theorem energy_preserving_inner
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪testToL2 F d (A f), testToL2 F d (A g)⟫_ℂ =
      ⟪testToL2 F d f, testToL2 F d g⟫_ℂ := by
  apply inner_eq_of_linear_norm_eq ((testToL2 F d).comp A) (testToL2 F d)
  intro h
  change ‖testToL2 F d (A h)‖ = ‖testToL2 F d h‖
  rw [testToL2_norm, testToL2_norm, hA]

end

/-! Weakly continuous unitary families are continuous in the actual observation topology. -/

open scoped InnerProductSpace ComplexConjugate

variable {F P : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [TopologicalSpace P]

theorem unitaryFamily_distance_continuous {d : ℕ}
    (A : P → Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ p f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A p f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hw : ∀ f k, Continuous (fun p => ⟪testToL2 F d k, testToL2 F d (A p f)⟫_ℂ))
    (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Continuous (fun p => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F d (A p f - k))) := by
  have hn (p : P) : ‖testToL2 F d (A p f)‖ = ‖testToL2 F d f‖ := by
    rw [testToL2_norm, testToL2_norm, hA]
  have heq (p : P) : Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F d (A p f - k)) =
      Real.sqrt (‖testToL2 F d f‖ ^ 2 -
        2 * (⟪testToL2 F d k, testToL2 F d (A p f)⟫_ℂ).re + ‖testToL2 F d k‖ ^ 2) := by
    rw [← testToL2_norm, map_sub, ← hn p]
    have hsq := norm_sub_sq (𝕜 := ℂ) (testToL2 F d (A p f)) (testToL2 F d k)
    rw [inner_re_symm] at hsq
    change ‖testToL2 F d (A p f) - testToL2 F d k‖ ^ 2 =
      ‖testToL2 F d (A p f)‖ ^ 2 -
        2 * (⟪testToL2 F d k, testToL2 F d (A p f)⟫_ℂ).re + ‖testToL2 F d k‖ ^ 2 at hsq
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [heq]
  exact (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp (hw f k)))).add continuous_const |>.sqrt

theorem unitaryFamily_inverse_weak_continuous {d : ℕ}
    (A : P → Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ p f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A p f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hw : ∀ f k, Continuous (fun p => ⟪testToL2 F d k, testToL2 F d (A p f)⟫_ℂ))
    (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Continuous (fun p => ⟪testToL2 F d k, testToL2 F d ((A p).symm f)⟫_ℂ) := by
  have heq (p : P) : ⟪testToL2 F d k, testToL2 F d ((A p).symm f)⟫_ℂ =
      conj (⟪testToL2 F d f, testToL2 F d (A p k)⟫_ℂ) := by
    rw [← energy_preserving_inner F d (A p).toLinearMap (hA p)]
    change ⟪testToL2 F d (A p k), testToL2 F d (A p ((A p).symm f))⟫_ℂ = _
    rw [(A p).apply_symm_apply, inner_conj_symm]
  simp_rw [heq]
  exact (hw k f).star

theorem circleExtension_continuous_of_weak
    {E : Type} [NormedField E] [Algebra F E] {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) (a : P → Oscillator.Construction.CircleExtension σ H K c ψ)
    (hp : Continuous (fun p => Oscillator.Construction.circleProjection σ H K c ψ (a p)))
    (hw : ∀ f k, Continuous (fun p =>
      ⟪testToL2 F (m * n) k, testToL2 F (m * n) ((a p).val.2 f)⟫_ℂ)) : Continuous a := by
  let A := fun p => (a p).val.2
  have hA (p : P) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) : Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (A p f) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f :=
    (a p).property.1 f
  have hi (p : P) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
      Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) ((A p).symm f) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f := by
    rw [← hA p ((A p).symm f), (A p).apply_symm_apply]
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk hp
  apply Continuous.prodMk
  · apply continuous_pi
    rintro ⟨f, k⟩
    exact unitaryFamily_distance_continuous A hA hw f k
  · apply continuous_pi
    rintro ⟨f, k⟩
    exact unitaryFamily_distance_continuous (fun p => (A p).symm) hi
      (unitaryFamily_inverse_weak_continuous A hA hw) f k

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Weak.Construction
