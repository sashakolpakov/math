import OAI.RepresentationTheory.Weil.Local.DensityMeasure
import OAI.RepresentationTheory.Weil.Local.RealWeyl
import OAI.RepresentationTheory.Weil.Local.ComplexWeyl
import OAI.RepresentationTheory.Weil.Local.SchurIndicators

/-! # Oscillator Schur -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatorSchur.Construction

noncomputable section

/-! Scalarity of the oscillator kernel from its actual energy and Heisenberg action. -/

theorem schwartzBruhat_translate_mem
    {k : Type} [NormedField k] {n : ℕ} (q : FunctionsMetaplectic.Construction.Position k n)
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (fun x => f (x - q)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨r, e, φ, rfl⟩
      · exact FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous (continuous_id.sub continuous_const))
          (hf.2.comp_homeomorph (Homeomorph.subRight q))
      · have hh := FunctionsMetaplectic.Construction.schwartz_coordinate_mem e (φ.compSubConstCLM ℂ (e.symm q))
        convert hh using 1
        funext x
        change φ (e.symm (x - q)) = φ (e.symm x - e.symm q)
        rw [map_sub]
  | zero => exact (FunctionsMetaplectic.Construction.schwartzBruhat k n).zero_mem
  | add f g _ _ hf hg => exact (FunctionsMetaplectic.Construction.schwartzBruhat k n).add_mem hf hg
  | smul c f _ hf => exact (FunctionsMetaplectic.Construction.schwartzBruhat k n).smul_mem c hf

theorem oscillator_kernel_scalar_of_modulation_stability
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (hStable : ∀ (p : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n),
      (fun x => ψ (FunctionsMetaplectic.Construction.dot p x) * f.val x) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection k n ψ a = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.2 f = z • f := by
  let M (p : FunctionsMetaplectic.Construction.Position k n) : FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n := {
    toFun f := ⟨fun x => ψ (FunctionsMetaplectic.Construction.dot p x) * f.val x, hStable p f⟩
    map_add' f g := by apply Subtype.ext; funext x; exact mul_add _ _ _
    map_smul' z f := by apply Subtype.ext; funext x; exact mul_left_comm _ _ _ }
  have hM (p : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
      (M p f).val x = ModulationMeasure.Construction.modulationCharacter ψ p x * f.val x := rfl
  have hA (p : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : a.val.2 (M p f) = M p (a.val.2 f) := by
    have hgraph : FunctionsMetaplectic.Construction.heisenbergGraph ψ (Sum.elim 0 p) f (M p f) := by
      unfold FunctionsMetaplectic.Construction.heisenbergGraph
      exact (SchurIndicators.Construction.heisenberg_pure_modulation ψ p f.val).symm
    have h := (a.property.2 (Sum.elim 0 p) f (M p f)).mp hgraph
    have hp : a.val.1 = 1 := ha
    rw [hp, FunctionsMetaplectic.Construction.symplecticAction_one] at h
    apply Subtype.ext
    exact h.trans (SchurIndicators.Construction.heisenberg_pure_modulation ψ p (a.val.2 f).val)
  have hnorm (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) : ‖(a.val.2 f).val x‖ = ‖f.val x‖ :=
    DensityMeasure.Construction.energy_commutant_preserves_norm k ψ hc hu hn M hM a.val.2.toLinearMap a.property.1 hA f x
  have hzero (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) (hx : f.val x = 0) : (a.val.2 f).val x = 0 := by
    apply norm_eq_zero.mp
    rw [hnorm, hx, norm_zero]
  by_cases he : ∃ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, f ≠ 0
  · obtain ⟨u, hu0⟩ := he
    obtain ⟨y, hy⟩ : ∃ y, u.val y ≠ 0 := by
      by_contra! h
      exact hu0 (Subtype.ext (funext h))
    let z : ℂ := (a.val.2 u).val y / u.val y
    have hz : ‖z‖ = 1 := by rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hy)]
    refine ⟨z, hz, fun f => ?_⟩
    apply Subtype.ext
    funext x
    let t : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun w => u.val (w - (x - y)), schwartzBruhat_translate_mem _ u.property⟩
    have ht : t.val x = u.val y := by change u.val (x - (x - y)) = _; simp
    have hAt : (a.val.2 t).val x = (a.val.2 u).val y := by
      have hgraph : FunctionsMetaplectic.Construction.heisenbergGraph ψ (Sum.elim (x - y) 0) u t := by
        funext w
        simp [FunctionsMetaplectic.Construction.heisenbergFunction, t, Pi.sub_def]
      have h := (a.property.2 (Sum.elim (x - y) 0) u t).mp hgraph
      have hp : a.val.1 = 1 := ha
      rw [hp, FunctionsMetaplectic.Construction.symplecticAction_one] at h
      have hh := congrFun h x
      simpa [FunctionsMetaplectic.Construction.heisenbergFunction, Pi.sub_def] using hh
    have hh := hzero (f - (f.val x / u.val y) • t) x (by
      change f.val x - (f.val x / u.val y) * t.val x = 0
      rw [ht, div_mul_cancel₀ _ hy, sub_self])
    rw [map_sub, map_smul] at hh
    change (a.val.2 f).val x - (f.val x / u.val y) * (a.val.2 t).val x = 0 at hh
    rw [hAt] at hh
    change (a.val.2 f).val x = z * f.val x
    rw [sub_eq_zero] at hh
    rw [hh]
    dsimp [z]
    ring
  · refine ⟨1, norm_one, fun f => ?_⟩
    have hf : f = 0 := by by_contra h; exact he ⟨f, h⟩
    rw [hf, map_zero, smul_zero]

theorem real_oscillator_kernel_scalar {n : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection ℝ n ψ a = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.2 f = z • f := by
  obtain ⟨c, hc', rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  apply oscillator_kernel_scalar_of_modulation_stability (Gaussian.Construction.realCharacter c) hc hu hn _ a ha
  intro p f
  have h := RealWeyl.Construction.real_modulation_mem c f (-p)
  have hd (x : FunctionsMetaplectic.Construction.Position ℝ n) : -FunctionsMetaplectic.Construction.dot (-p) x = FunctionsMetaplectic.Construction.dot p x := by simp [FunctionsMetaplectic.Construction.dot]
  simp only [hd] at h
  simpa only [mul_comm] using h

theorem complex_oscillator_kernel_scalar {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : FunctionsMetaplectic.Construction.Oscillator ℂ n ψ) (ha : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ a = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n, a.val.2 f = z • f := by
  apply oscillator_kernel_scalar_of_modulation_stability ψ hc hu hn _ a ha
  intro p f
  have h := ComplexWeyl.Construction.complex_modulation_mem ψ hc hu f (-p)
  have hd (x : FunctionsMetaplectic.Construction.Position ℂ n) : -FunctionsMetaplectic.Construction.dot (-p) x = FunctionsMetaplectic.Construction.dot p x := by simp [FunctionsMetaplectic.Construction.dot]
  simp only [hd] at h
  simpa only [mul_comm] using h

end

end OAI.RepresentationTheory.Weil.Local.OscillatorSchur.Construction
