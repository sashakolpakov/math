import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel
import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification
import OAI.RepresentationTheory.Weil.Local.OscillatorSchur

/-! # Bruhat Products -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts.LocalAnalysis

noncomputable section

/-! Products and translated correlations in the actual local Bruhat space. -/

open scoped SchwartzMap ComplexConjugate

theorem bruhat_conjugate_mem {k : Type} [NormedField k] {N : ℕ}
    {f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (fun x => conj (f x)) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hf.1.comp _) (hf.2.comp_left (map_zero _))
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem e (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap)
  | zero => simpa only [Pi.zero_apply, map_zero] using! (Local.FunctionsMetaplectic.Construction.schwartzBruhat k N).zero_mem
  | add f g _ _ hf hg =>
      simpa only [Pi.add_apply, map_add] using! (Local.FunctionsMetaplectic.Construction.schwartzBruhat k N).add_mem hf hg
  | smul c f _ hf =>
      simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using! (Local.FunctionsMetaplectic.Construction.schwartzBruhat k N).smul_mem (conj c) hf

theorem schwartzBruhat_archimedean_mul_mem
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    {N : ℕ} {f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ}
    (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hh : h ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (fun x => f x * h x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  obtain ⟨φ, rfl⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp hf
  obtain ⟨χ, rfl⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp hh
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨SchwartzMap.smulLeftCLM ℂ φ χ, ?_⟩
  funext x
  exact (SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth χ x).symm

theorem schwartzBruhat_mul_fieldTransport
    {k l : Type} [NormedField k] [NormedField l] {N : ℕ}
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (hmul : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N, (fun x => f.val x * h.val x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat l N)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : (fun x => f.val x * h.val x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi
  let f' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N := ⟨f.val ∘ p.symm, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm f.property⟩
  let h' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N := ⟨h.val ∘ p.symm, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm h.property⟩
  have hh := FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p (hmul f' h')
  convert hh using 1
  funext x
  change f.val x * h.val x = f.val (p.symm (p x)) * h.val (p.symm (p x))
  rw [p.symm_apply_apply]

theorem schwartzBruhat_mul_mem
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    {N : ℕ} (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (fun x => f.val x * h.val x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k := IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    obtain ⟨hf, hs⟩ := NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp f.property
    obtain ⟨hh, _⟩ := NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp h.property
    exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hf.mul hh) hs.mul_right
  · rcases Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, hi⟩ | ⟨e, he, hi⟩
    · exact schwartzBruhat_mul_fieldTransport e he hi
        (fun f h => schwartzBruhat_archimedean_mul_mem f.property h.property) f h
    · exact schwartzBruhat_mul_fieldTransport e he hi
        (fun f h => schwartzBruhat_archimedean_mul_mem f.property h.property) f h

def bruhatCorrelation
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    {N : ℕ} (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat k N :=
  ⟨fun x => f.val (x - q) * conj (h.val (x + q)),
    schwartzBruhat_mul_mem
      ⟨_, Local.OscillatorSchur.Construction.schwartzBruhat_translate_mem q f.property⟩
      ⟨_, bruhat_conjugate_mem (by
        simpa only [sub_neg_eq_add] using Local.OscillatorSchur.Construction.schwartzBruhat_translate_mem (-q) h.property)⟩⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.BruhatProducts.LocalAnalysis
