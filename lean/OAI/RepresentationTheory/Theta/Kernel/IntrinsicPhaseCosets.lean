import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz

/-! # Intrinsic Phase Cosets -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseCosets.Intrinsic

noncomputable section

/-! Construction of a native finite-Schwartz input from a phase that is
constant on sufficiently small rational cosets inside the input support.
This helper turns arithmetic phase periods into actual restricted tensors. -/

open scoped _root_.NumberField Classical BigOperators

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem native_phase_input (f : Adelic.FiniteSchwartz.finiteSchwartz F N)
    (phase : (Fin N → F) → ℂ) (M : ℕ) (hM : 0 < M)
    (hperiod : ∀ u ∈ Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) (by exact_mod_cast hM.ne'),
      ∀ x, Adelic.Evaluation.finiteSchwartzFunction F N f (u + x) = Adelic.Evaluation.finiteSchwartzFunction F N f x)
    (hphase : ∀ x y : Fin N → F,
      Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) ≠ 0 →
      Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition y ∈
        Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) (by exact_mod_cast hM.ne') → phase x = phase y) :
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F N, ∀ x : Fin N → F,
      Adelic.Evaluation.finiteSchwartzFunction F N g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        phase x * Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  let hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨s,hs⟩ := Weil.AdelicSplitting.FiniteCosets.Construction.finite_function_coset_expansion (Adelic.Evaluation.finiteSchwartzFunction F N f)
    (Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).2 (M : F) hMF hperiod
  let a (c : Weil.AdelicSplitting.FiniteCosets.Construction.FinitePositionQuotient (ι := Fin N) (M : F) hMF) :=
    Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionQuotientRep (M : F) hMF c
  let g : Adelic.FiniteSchwartz.finiteSchwartz F N := ∑ c ∈ s,
    (phase (a c) * Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))) •
      Intrinsic.OneFormsIntrinsic.cosetInput F N (M : F) hMF (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))
  refine ⟨g,?_⟩
  intro x
  change Adelic.Evaluation.finiteSchwartzFunction F N (∑ c ∈ s,
    (phase (a c) * Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))) •
      Intrinsic.OneFormsIntrinsic.cosetInput F N (M : F) hMF (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))) (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) = _
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Intrinsic.OneFormsIntrinsic.cosetInput_value]
  rw [hs (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (phase (a c) * Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))) *
      Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator (M : F) hMF (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
    phase x * (Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) *
      Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator (M : F) hMF (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x))
  by_cases hc : Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) = 0
  · simp only [hc, mul_zero, zero_mul]
  by_cases hm : Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c) ∈
      Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) hMF
  · have he : Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) := by
      simpa only [sub_add_cancel] using hperiod _ hm (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))
    have hφ := hphase x (a c) (he.trans_ne hc) hm
    rw [← hφ]
    ring
  · have hi : Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator (M : F) hMF
        (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) = 0 := by
      exact Set.indicator_of_notMem hm (fun _ => (1 : ℂ))
    simp only [hi, mul_zero]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseCosets.Intrinsic
