import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Compact Character -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter.LocalAnalysis

noncomputable section

section

/-! Character orthogonality on additive subgroups for local Fourier inversion. -/

open _root_.MeasureTheory
open scoped Classical

theorem integral_character_subgroup
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (U : OpenAddSubgroup E)
    (χ : AddChar E ℂ) :
    (∫ x in (U : Set E), χ x ∂μ) =
      if ∀ x ∈ U, χ x = 1 then (μ.real (U : Set E) : ℂ) else 0 := by
  by_cases hχ : ∀ x ∈ U, χ x = 1
  · rw [ite_eq_left hχ]
    calc
      _ = ∫ _ in (U : Set E), (1 : ℂ) ∂μ :=
        setIntegral_congr_fun U.isOpen.measurableSet (fun x hx => hχ x hx)
      _ = _ := by simp
  · rw [ite_eq_right hχ]
    push Not at hχ
    obtain ⟨a, ha, hχa⟩ := hχ
    let f : E → ℂ := (U : Set E).indicator (fun x => χ x)
    have hfun : (fun x => f (x + a)) = fun x => χ a * f x := by
      funext x
      have hmem : x + a ∈ U ↔ x ∈ U := U.add_mem_cancel_right ha
      by_cases hx : x ∈ U
      · simp [f, hx, hmem.mpr hx, χ.map_add_eq_mul, mul_comm]
      · simp [f, hx, show x + a ∉ U from fun h => hx (hmem.mp h)]
    have h := integral_add_right_eq_self (μ := μ) f a
    rw [hfun, integral_const_mul] at h
    have hf : (∫ x, f x ∂μ) = 0 := by
      by_contra hne
      apply hχa
      apply mul_right_cancel₀ hne
      simpa using h
    simpa only [f, integral_indicator U.isOpen.measurableSet] using hf

def additiveAnnihilator
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ) (U : AddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) :
    AddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n) where
  carrier := {x | ∀ y ∈ U, ψ (Local.FunctionsMetaplectic.Construction.dot x y) = 1}
  zero_mem' := by simp [Local.FunctionsMetaplectic.Construction.dot]
  add_mem' {x z} hx hz y hy := by
    have hdot : Local.FunctionsMetaplectic.Construction.dot (x + z) y = Local.FunctionsMetaplectic.Construction.dot x y + Local.FunctionsMetaplectic.Construction.dot z y := by
      simp [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hdot, ψ.map_add_eq_mul, hx y hy, hz y hy, one_mul]
  neg_mem' {x} hx y hy := by
    have hdot : Local.FunctionsMetaplectic.Construction.dot (-x) y = -Local.FunctionsMetaplectic.Construction.dot x y := by simp [Local.FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
    rw [hdot, ψ.map_neg_eq_inv, hx y hy, inv_one]

theorem integral_pairing_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    (∫ y in (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)), ψ (Local.FunctionsMetaplectic.Construction.dot x y) ∂μ) =
      if x ∈ additiveAnnihilator ψ U.toAddSubgroup then (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 := by
  let χ : AddChar (Local.FunctionsMetaplectic.Construction.Position k n) ℂ :=
    ψ.compAddMonoidHom (dotProductBilin k k x).toAddMonoidHom
  exact integral_character_subgroup μ U χ

theorem fourier_indicator_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) x =
      if x ∈ additiveAnnihilator ψ U.toAddSubgroup then (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  have heq : (fun y => (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) =
      (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun y => ψ (Local.FunctionsMetaplectic.Construction.dot (-x) y)) := by
    funext y
    by_cases hy : y ∈ U <;> simp [hy, Local.FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
  rw [heq, integral_indicator U.isOpen.measurableSet, integral_pairing_subgroup]
  simp only [neg_mem_iff]

theorem subgroup_indicator_locallyConstant
    {E : Type*} [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (U : OpenAddSubgroup E) :
    IsLocallyConstant ((U : Set E).indicator (fun _ => (1 : ℂ))) := by
  have h := (LocallyConstant.charFn ℂ
    (show IsClopen (U : Set E) from ⟨U.isClosed, U.isOpen⟩)).isLocallyConstant
  change IsLocallyConstant ((U : Set E).indicator (1 : E → ℂ)) at h
  convert! h using 1

theorem subgroup_indicator_compactSupport
    {E : Type*} [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] [T2Space E]
    (U : OpenAddSubgroup E) (hU : IsCompact (U : Set E)) :
    HasCompactSupport ((U : Set E).indicator (fun _ => (1 : ℂ))) := by
  apply HasCompactSupport.intro hU
  intro x hx
  simp [hx]

theorem additiveAnnihilator_compact_open
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    [ProperSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k n))) :
    IsCompact (additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)) ∧
      IsOpen (additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)) := by
  let f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ := (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))
  have hf := subgroup_indicator_compactSupport U hU
  have hF := NonarchimedeanIntertwiner.LocalAnalysis.fourierIntegral_locallyConstant ψ
    (NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_character_locallyConstant ψ hu hc) μ hf
  have hμ : (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (ENNReal.toReal_pos _ hU.measure_ne_top).ne'
    exact (Measure.measure_pos_of_nonempty_interior μ
      (by rw [U.isOpen.interior_eq]; exact ⟨0, U.zero_mem⟩)).ne'
  have hann : (additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)) =
      {x | Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ)} := by
    ext x
    change x ∈ additiveAnnihilator ψ U.toAddSubgroup ↔
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) x = _
    rw [fourier_indicator_subgroup]
    by_cases hx : x ∈ additiveAnnihilator ψ U.toAddSubgroup <;> simp [hx, hμ.symm]
  have hclosed : IsClosed (additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)) := by
    rw [hann]
    exact hF.isClosed_fiber _
  have hcompact := NonarchimedeanIntertwiner.LocalAnalysis.fourierIntegral_compactSupport_of_locallyConstant ψ hn μ
    (subgroup_indicator_locallyConstant U) hf
  constructor
  · apply hcompact.of_isClosed_subset hclosed
    intro x hx
    apply subset_tsupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)
    have hx' := congrArg (fun S : Set (Local.FunctionsMetaplectic.Construction.Position k n) => x ∈ S) hann
    have heq : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) := by
      exact (Eq.mp hx' hx)
    change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x ≠ 0
    rwa [heq]
  · rw [hann]
    exact hF.isOpen_fiber _

end

/-! A vacuum-fixed oscillator constrains the character annihilator through
its momentum-to-position matrix entries. -/

open scoped Classical

section Algebra
variable {k : Type} [Field k] (R : Subring k) (n : ℕ)

def ringVacuum : Local.FunctionsMetaplectic.Construction.Position k n → ℂ :=
  (Set.univ.pi (fun _ : Fin n => (R : Set k))).indicator (fun _ => 1)

theorem ringVacuum_zero : ringVacuum R n 0 = 1 := by
  simp [ringVacuum]

theorem heisenberg_ringVacuum_single
    (ψ : AddChar k ℂ) (j : Fin n) (u : k) (hu : ∀ t ∈ R, ψ (u * t) = 1) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Pi.single (.inr j) u) (ringVacuum R n) = ringVacuum R n := by
  funext x
  have he : Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Pi.single (.inr j) u) (ringVacuum R n) x =
      ψ (u * x j) * ringVacuum R n x := by
    simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, Pi.single_apply]
  rw [he]
  by_cases hx : x ∈ Set.univ.pi (fun _ : Fin n => (R : Set k))
  · rw [hu _ (hx j (Set.mem_univ j)), one_mul]
  · simp [ringVacuum, hx]

theorem heisenberg_ringVacuum_fixed_position
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n)
    (h : Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (ringVacuum R n) = ringVacuum R n) :
    ∀ i, v (.inl i) ∈ R := by
  let q : Local.FunctionsMetaplectic.Construction.Position k n := fun i => v (.inl i)
  have he := congrFun h q
  have hz : (fun i => q i - v (.inl i)) = (0 : Local.FunctionsMetaplectic.Construction.Position k n) := by ext i; simp [q]
  change ψ (∑ i, v (.inr i) * (q i - v (.inl i) / 2)) *
    ringVacuum R n (fun i => q i - v (.inl i)) = ringVacuum R n q at he
  rw [hz, ringVacuum_zero, mul_one] at he
  have hn : ringVacuum R n q ≠ 0 := by
    intro hh
    have ht := hu (∑ i, v (.inr i) * (q i - v (.inl i) / 2))
    rw [he, hh, norm_zero] at ht
    exact zero_ne_one ht
  have hq : q ∈ Set.univ.pi (fun _ : Fin n => (R : Set k)) := by
    by_contra hq
    exact hn (Set.indicator_of_notMem hq _)
  intro i
  exact hq i (Set.mem_univ i)

end Algebra

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] {n : ℕ}

theorem vacuum_fixed_oscillator_mixing
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (R : Subring k)
    (φ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (hφ : φ.val = ringVacuum R n)
    (T : Local.FunctionsMetaplectic.Construction.Oscillator k n ψ) (hT : T.val.2 φ = φ)
    (i j : Fin n) (u : k) (huR : ∀ t ∈ R, ψ (u * t) = 1) :
    T.val.1.val (.inl i) (.inr j) * u ∈ R := by
  let v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n := Pi.single (.inr j) u
  have hv : Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v φ φ := by
    change φ.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v φ.val
    rw [hφ]
    exact (heisenberg_ringVacuum_single R n ψ j u huR).symm
  have ht := (T.property.2 v φ φ).mp hv
  change (T.val.2 φ).val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction T.val.1 v) (T.val.2 φ).val at ht
  rw [hT, hφ] at ht
  have h := heisenberg_ringVacuum_fixed_position R n ψ hu (Local.FunctionsMetaplectic.Construction.symplecticAction T.val.1 v) ht.symm i
  simpa [v, Local.FunctionsMetaplectic.Construction.symplecticAction, Matrix.mulVec, dotProduct, Pi.single_apply] using h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter.LocalAnalysis
