import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterCutoff
import OAI.AlgebraicGeometry.Comparison.Betti.ParameterFamilyGermCongruence
import OAI.AlgebraicGeometry.Comparison.Betti.MixedJetDifferential

/-! # Mixed Jet Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.MixedJetDifferential.Dolbeault

noncomputable section

section

/-! The actual mixed-jet differential and smoothness on open parameter
domains, obtained by equality with smooth extensions near each parameter. -/

open Set Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

omit [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P] [CompleteSpace F] in
theorem mixedParameterJet_eventuallyEq_of_family_germ {g h : P × ℂ → F} {p : P}
    (he : ∀ᶠ t in 𝓝 p, ∀ z, g (t, z) = h (t, z)) (k l : ℕ) (z : ℂ) :
    MixedJetAlgebra.Dolbeault.mixedParameterJet g k l =ᶠ[𝓝 (p, z)] MixedJetAlgebra.Dolbeault.mixedParameterJet h k l := by
  have hnear : ∀ᶠ t in 𝓝 p, ∀ᶠ r in 𝓝 t, ∀ w, g (r, w) = h (r, w) := he.eventually_nhds
  have hfirst : Tendsto (Prod.fst : P × ℂ → P) (𝓝 (p, z)) (𝓝 p) := continuousAt_fst
  filter_upwards [hfirst.eventually hnear] with y hy
  exact ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hy k l y.2

theorem hasFDerivAt_mixedParameterJet_on {S : Set P} (hS : IsOpen S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ))
    {U : Set ℂ} (hU : IsOpen U) (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) {q : P × ℂ} (hq : q ∈ S ×ˢ U) :
    HasFDerivAt (MixedJetAlgebra.Dolbeault.mixedParameterJet g k l)
      (MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) k (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l q) +
        MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) k (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) q)) q := by
  obtain ⟨G, hG, hGhol, he⟩ := ParameterCutoff.Dolbeault.exists_global_smooth_family_extension hS isClosed_singleton
    (singleton_subset_iff.mpr hq.1) hg hhol
  have hfamily : ∀ᶠ t in 𝓝 q.1, ∀ z, G (t, z) = g (t, z) := by
    simpa only [nhdsSet_singleton] using he
  have hjet := mixedParameterJet_eventuallyEq_of_family_germ hfamily k l q.2
  have hd := (MixedJetDifferential.Dolbeault.hasFDerivAt_mixedParameterJet hG hU hGhol k l hq.2).congr_of_eventuallyEq hjet.symm
  have hp : MixedJetAlgebra.Dolbeault.mixedParameterJet G (k + 1) l q = MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l q :=
    ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hfamily (k + 1) l q.2
  have hl : MixedJetAlgebra.Dolbeault.mixedParameterJet G k (l + 1) q = MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) q :=
    ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hfamily k (l + 1) q.2
  rw [hp, hl] at hd
  exact hd

theorem mixedParameterJet_smoothOn {S : Set P} (hS : IsOpen S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ))
    {U : Set ℂ} (hU : IsOpen U) (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) : ContDiffOn ℝ ∞ (MixedJetAlgebra.Dolbeault.mixedParameterJet g k l) (S ×ˢ U) := by
  intro q hq
  obtain ⟨G, hG, hGhol, he⟩ := ParameterCutoff.Dolbeault.exists_global_smooth_family_extension hS isClosed_singleton
    (singleton_subset_iff.mpr hq.1) hg hhol
  have hfamily : ∀ᶠ t in 𝓝 q.1, ∀ z, G (t, z) = g (t, z) := by
    simpa only [nhdsSet_singleton] using he
  have hs := (MixedJetAlgebra.Dolbeault.mixedParameterJet_smooth hG hU hGhol k l).contDiffAt
    ((isOpen_univ.prod hU).mem_nhds (show q ∈ univ ×ˢ U from ⟨mem_univ _, hq.2⟩))
  exact (hs.congr_of_eventuallyEq
    (mixedParameterJet_eventuallyEq_of_family_germ hfamily k l q.2).symm).contDiffWithinAt

end

/-! Linearity of the original mixed derivative arrays for smooth
holomorphic families on an open parameter domain. -/

open Set Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem mixedParameterJet_sub_on {S : Set P} (hS : IsOpen S) {g h : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) (hh : ContDiffOn ℝ ∞ h (S ×ˢ univ))
    {U : Set ℂ} (hU : IsOpen U)
    (hgol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => h (p, z)) U)
    (k l : ℕ) {q : P × ℂ} (hq : q ∈ S ×ˢ U) :
    MixedJetAlgebra.Dolbeault.mixedParameterJet (fun y => g y - h y) k l q =
      MixedJetAlgebra.Dolbeault.mixedParameterJet g k l q - MixedJetAlgebra.Dolbeault.mixedParameterJet h k l q := by
  obtain ⟨G, hG, hGol, heG⟩ := ParameterCutoff.Dolbeault.exists_global_smooth_family_extension hS isClosed_singleton
    (singleton_subset_iff.mpr hq.1) hg hgol
  obtain ⟨H, hH, hHol, heH⟩ := ParameterCutoff.Dolbeault.exists_global_smooth_family_extension hS isClosed_singleton
    (singleton_subset_iff.mpr hq.1) hh hhol
  have hfG : ∀ᶠ t in 𝓝 q.1, ∀ z, G (t, z) = g (t, z) := by
    simpa only [nhdsSet_singleton] using heG
  have hfH : ∀ᶠ t in 𝓝 q.1, ∀ z, H (t, z) = h (t, z) := by
    simpa only [nhdsSet_singleton] using heH
  have hpair : ∀ᶠ t in 𝓝 q.1, ∀ z, G (t, z) - H (t, z) = g (t, z) - h (t, z) := by
    filter_upwards [hfG, hfH] with t htG htH
    intro z
    rw [htG z, htH z]
  have hs := MixedJetAlgebra.Dolbeault.mixedParameterJet_sub (q := q) hG hH hU hGol hHol k l hq.2
  change iteratedDeriv l (fun z => OperatorParameterJets.Dolbeault.parameterJet (fun y => G y - H y) k (q.1, z)) q.2 =
    iteratedDeriv l (fun z => OperatorParameterJets.Dolbeault.parameterJet G k (q.1, z)) q.2 -
    iteratedDeriv l (fun z => OperatorParameterJets.Dolbeault.parameterJet H k (q.1, z)) q.2 at hs
  rw [ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ (g := fun y => G y - H y) (h := fun y => g y - h y) hpair,
    ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hfG, ParameterFamilyGermCongruence.Dolbeault.mixedParameterJet_eq_of_family_germ hfH] at hs
  exact hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.MixedJetDifferential.Dolbeault
