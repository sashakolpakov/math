import OAI.RepresentationTheory.Weil.Local.SpecialLinearCommutators
import OAI.RepresentationTheory.Weil.Local.AnnihilatorDuality

/-! # Schur Indicators -/

namespace OAI.RepresentationTheory.Weil.Local.SchurIndicators.Construction

noncomputable section

/-! Compact-open indicator eigenspaces for the nonarchimedean oscillator kernel. -/

open _root_.MeasureTheory
open scoped Classical

theorem heisenberg_pure_translation
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (t : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim (-t) 0) f = fun x => f (x + t) := by
  funext x
  simp [FunctionsMetaplectic.Construction.heisenbergFunction, Pi.add_def]

theorem heisenberg_pure_modulation
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (t : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 t) f = fun x => ψ (FunctionsMetaplectic.Construction.dot t x) * f x := by
  funext x
  simp [FunctionsMetaplectic.Construction.heisenbergFunction, FunctionsMetaplectic.Construction.dot]

theorem oscillator_kernel_heisenberg
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k ℂ)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hh : h.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val) :
    (g.val.2 h).val = FunctionsMetaplectic.Construction.heisenbergFunction ψ v (g.val.2 f).val := by
  have hgraph := (g.property.2 v f h).mp hh
  have hproj : g.val.1 = 1 := hg
  rw [hproj, FunctionsMetaplectic.Construction.symplecticAction_one] at hgraph
  exact hgraph

theorem oscillator_kernel_indicator_eigenvector
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n))) :
    let f : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
      FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
        (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU)⟩
    ∀ x, (g.val.2 f).val x = (g.val.2 f).val 0 * f.val x := by
  intro f x
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have htranslation (t : FunctionsMetaplectic.Construction.Position k n) (ht : t ∈ U) :
      ∀ y, (g.val.2 f).val (y + t) = (g.val.2 f).val y := by
    have hh : f.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim (-t) 0) f.val := by
      rw [heisenberg_pure_translation]
      funext y
      have hmem : y + t ∈ U ↔ y ∈ U := U.add_mem_cancel_right ht
      by_cases hy : y ∈ U
      · simp [f, hy, hmem.mpr hy]
      · have hyt : y + t ∉ U := fun h => hy (hmem.mp h)
        simp [f, hy, hyt]
    have h := oscillator_kernel_heisenberg ψ g hg (Sum.elim (-t) 0) f f hh
    rw [heisenberg_pure_translation] at h
    exact fun y => (congrFun h y).symm
  have hmodulation (p : FunctionsMetaplectic.Construction.Position k n) (hp : p ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup) :
      ∀ y, (g.val.2 f).val y = ψ (FunctionsMetaplectic.Construction.dot p y) * (g.val.2 f).val y := by
    have hh : f.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 p) f.val := by
      rw [heisenberg_pure_modulation]
      funext y
      by_cases hy : y ∈ U
      · simp [f, hy, hp y hy]
      · simp [f, hy]
    have h := oscillator_kernel_heisenberg ψ g hg (Sum.elim 0 p) f f hh
    rw [heisenberg_pure_modulation] at h
    exact fun y => congrFun h y
  by_cases hx : x ∈ U
  · have h := htranslation x hx 0
    simpa [f, hx] using h
  · have hzero : (g.val.2 f).val x = 0 := by
      by_contra hz
      have hdouble : x ∈ CompactCharacter.Construction.additiveAnnihilator ψ (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup) := by
        intro p hp
        rw [FourierTools.Construction.dot_comm]
        apply mul_right_cancel₀ hz
        simpa only [one_mul] using (hmodulation p hp x).symm
      let μ : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
      let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
      obtain ⟨_, _, hduality⟩ := AnnihilatorDuality.Construction.nonarchimedean_annihilator_duality_and_scale hNondiscrete n ψ hu hc hn μ
      rw [(hduality U hU).1] at hdouble
      exact hx hdouble
    simp [f, hx, hzero]

end

end OAI.RepresentationTheory.Weil.Local.SchurIndicators.Construction
