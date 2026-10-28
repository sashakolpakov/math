import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter

/-! # Local Coset Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis

noncomputable section

/-! Exact Fourier transforms of compact open additive cosets. The
coefficient is a positive Haar volume and the phase is the actual character. -/

open _root_.MeasureTheory
open scoped Classical

variable {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
variable [SecondCountableTopology k] {N : ℕ}
variable (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
variable (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k N))

def localCosetIndicator (a : Local.FunctionsMetaplectic.Construction.Position k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)).indicator (fun _ => 1) (x - a)

theorem fourier_localCosetIndicator (a ξ : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (localCosetIndicator U a) ξ =
      if ξ ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup then
        (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) : ℂ) * ψ (-Local.FunctionsMetaplectic.Construction.dot ξ a) else 0 := by
  change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)).indicator (fun _ => 1) (x - a)) ξ = _
  simp only [sub_eq_add_neg]
  rw [NonarchimedeanIntertwiner.LocalAnalysis.fourierIntegral_translate, CompactCharacter.LocalAnalysis.fourier_indicator_subgroup]
  have hd : Local.FunctionsMetaplectic.Construction.dot ξ (-a) = -Local.FunctionsMetaplectic.Construction.dot ξ a := by simp [Local.FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
  rw [hd]
  split_ifs <;> ring

omit [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem localCosetIndicator_mem [LocallyCompactSpace k] (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)))
    (a : Local.FunctionsMetaplectic.Construction.Position k N) : localCosetIndicator U a ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  have hf := CompactCharacter.LocalAnalysis.subgroup_indicator_locallyConstant U
  have hs := CompactCharacter.LocalAnalysis.subgroup_indicator_compactSupport U hU
  apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hf.comp_continuous (continuous_id.sub continuous_const))
  exact hs.comp_homeomorph (Homeomorph.subRight a)

omit [BorelSpace k] [SecondCountableTopology k] in
theorem compactOpenSubgroup_volume_pos (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k N))) :
    0 < μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) := by
  apply ENNReal.toReal_pos
  · exact (U.isOpen.measure_pos μ ⟨0, U.zero_mem⟩).ne'
  · exact hU.measure_ne_top

theorem fourier_localCosetIndicator_zero (a : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (localCosetIndicator U a) 0 = (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) : ℂ) := by
  rw [fourier_localCosetIndicator, ite_eq_left (AddSubgroup.zero_mem _)]
  simp [Local.FunctionsMetaplectic.Construction.dot]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis
