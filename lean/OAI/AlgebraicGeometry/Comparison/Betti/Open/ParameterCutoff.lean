import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Parameter Cutoff -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterCutoff.Dolbeault

noncomputable section

/-! Smooth cutoffs inside an open parameter domain and global extensions
that agree with an entire family near a prescribed closed parameter set. -/

open Set Filter
open scoped ContDiff _root_.Manifold _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem exists_parameterCutoff_near_closed {S K : Set P}
    (hS : IsOpen S) (hK : IsClosed K) (hKS : K ⊆ S) :
    ∃ χ : P → ℂ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ S ∧
      (∀ᶠ p in 𝓝ˢ K, χ p = 1) := by
  have hd : Disjoint Sᶜ K := disjoint_left.mpr fun _ hp hk => hp (hKS hk)
  obtain ⟨f, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, P) hS.isClosed_compl hK hd (n := ⊤)
  refine ⟨fun p => (f p : ℂ), Complex.ofRealCLM.contDiff.comp f.contMDiff.contDiff, ?_, ?_⟩
  · intro p hp
    by_contra hpS
    have hz : (fun y => (f y : ℂ)) =ᶠ[𝓝 p] 0 := by
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hpS)] with y hy
      simp only [hy, Complex.ofReal_zero, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp
  · filter_upwards [hone] with p hp
    simp only [hp, Complex.ofReal_one]

omit [FiniteDimensional ℝ P] in
theorem parameterCutoff_mul_smooth {S : Set P} (hS : IsOpen S)
    {χ : P → ℂ} (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) :
    ContDiff ℝ ∞ (fun q : P × ℂ => χ q.1 • g q) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hp : q.1 ∈ S
  · exact (hχ.contDiffAt.comp q contDiffAt_fst).smul
      (hg.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
  · have hzero : χ =ᶠ[𝓝 q.1] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hp (hsupp h))
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hzero.comp_tendsto continuousAt_fst] with y hy
    rw [show χ y.1 = 0 from hy, zero_smul]

omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem parameterCutoff_mul_holomorphic {S : Set P} {U : Set ℂ}
    {χ : P → ℂ} (hsupp : tsupport χ ⊆ S) {g : P × ℂ → F}
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) (p : P) :
    DifferentiableOn ℂ (fun z => χ p • g (p, z)) U := by
  by_cases hp : p ∈ S
  · exact (hhol p hp).const_smul (χ p)
  · have hzero : χ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
    simpa only [hzero, zero_smul] using
      (differentiableOn_const (c := (0 : F)) (𝕜 := ℂ) (s := U))

theorem exists_global_smooth_family_extension {S K : Set P} (hS : IsOpen S)
    (hK : IsClosed K) (hKS : K ⊆ S) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) {U : Set ℂ}
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) :
    ∃ G : P × ℂ → F, ContDiff ℝ ∞ G ∧
      (∀ p, DifferentiableOn ℂ (fun z => G (p, z)) U) ∧
      (∀ᶠ p in 𝓝ˢ K, ∀ z, G (p, z) = g (p, z)) := by
  obtain ⟨χ, hχ, hsupp, hone⟩ := exists_parameterCutoff_near_closed hS hK hKS
  refine ⟨fun q => χ q.1 • g q, parameterCutoff_mul_smooth hS hχ hsupp hg,
    parameterCutoff_mul_holomorphic hsupp hhol, ?_⟩
  filter_upwards [hone] with p hp
  intro z
  simp only [hp, one_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParameterCutoff.Dolbeault
