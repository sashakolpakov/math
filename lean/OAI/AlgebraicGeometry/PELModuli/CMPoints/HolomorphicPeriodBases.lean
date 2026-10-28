import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodBases
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Holomorphic Period Bases -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodBases

noncomputable section

/-! Holomorphic period sections give full integral lattice markings
whose basis vectors vary holomorphically on an open neighborhood. The
real coordinate maps remain continuous and span the complete kernels. -/

open Set _root_.Metric Filter
open scoped Classical _root_.Topology

variable {P V X Index : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [TopologicalSpace X] [Fintype Index]
  {G : P → Type} [∀ p, Group (G p)]
  {exponential : ∀ p, V → G p} {embed : ∀ p, G p → X} {p₀ : P}

theorem exists_holomorphic_real_period_basis_on
    (e₀ : (Index → ℝ) ≃L[ℝ] V)
    (hcontinue : ∀ i : Index, ∃ (U : Set P) (period : P → V),
      IsOpen U ∧ p₀ ∈ U ∧ DifferentiableOn ℂ period U ∧
        period p₀ = e₀ (Pi.single i 1) ∧ ∀ p ∈ U, exponential p (period p) = 1) :
    ∃ (U : Set P) (e : P → (Index → ℝ) ≃L[ℝ] V),
      IsOpen U ∧ p₀ ∈ U ∧ e p₀ = e₀ ∧
      ContinuousOn (fun p => (e p).toContinuousLinearMap) U ∧
      (∀ i, DifferentiableOn ℂ (fun p => e p (Pi.single i 1)) U) ∧
      ∀ p ∈ U, ∀ i, exponential p (e p (Pi.single i 1)) = 1 := by
  choose U period hU hpU hcont hcenter hker using hcontinue
  let B : Set P := ⋂ i, U i
  have hB : IsOpen B := isOpen_iInter_of_finite hU
  have hpB : p₀ ∈ B := mem_iInter.mpr hpU
  let frames := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) Index
  let f : P → (Index → ℝ) →L[ℝ] V := fun p => frames.symm (fun i => period i p)
  have hf : ContinuousOn f B := frames.symm.continuous.comp_continuousOn
    (continuousOn_pi.mpr (fun i => (hcont i).continuousOn.mono (iInter_subset U i)))
  have hf₀ : f p₀ = e₀.toContinuousLinearMap := by
    apply frames.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    exact hcenter i
  let invertible : Set ((Index → ℝ) →L[ℝ] V) :=
    range (fun e : (Index → ℝ) ≃L[ℝ] V => e.toContinuousLinearMap)
  have hinv : f ⁻¹' invertible ∈ 𝓝 p₀ := by
    apply (hf.continuousAt (hB.mem_nhds hpB)).preimage_mem_nhds
    rw [hf₀]
    exact e₀.nhds
  obtain ⟨W, hWsub, hW, hpW⟩ := _root_.mem_nhds_iff.mp hinv
  have hex (p : P) : ∃ e : (Index → ℝ) ≃L[ℝ] V,
      p ∈ W → e.toContinuousLinearMap = f p := by
    by_cases hp : p ∈ W
    · obtain ⟨e, he⟩ := hWsub hp
      exact ⟨e, fun _ => he⟩
    · exact ⟨e₀, fun h => (hp h).elim⟩
  choose e he using hex
  have he₀ : e p₀ = e₀ := by
    ext v
    exact congrArg (fun L : (Index → ℝ) →L[ℝ] V => L v) ((he p₀ hpW).trans hf₀)
  have hi (p : P) (hp : p ∈ B ∩ W) (i : Index) :
      e p (Pi.single i 1) = period i p := by
    have h := congrArg (fun L => frames L i) (he p hp.2)
    change e p (Pi.single i 1) = frames (frames.symm (fun j => period j p)) i at h
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  refine ⟨B ∩ W, e, hB.inter hW, ⟨hpB, hpW⟩, he₀,
    (hf.mono inter_subset_left).congr (fun p hp => he p hp.2), ?_, ?_⟩
  · intro i
    exact ((hcont i).mono (fun _ hp => mem_iInter.mp hp.1 i)).congr (fun p hp => hi p hp i)
  · intro p hp i
    rw [hi p hp i]
    exact hker i p ((mem_iInter.mp hp.1) i)

theorem exists_holomorphic_full_period_bases_on
    (H : ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀)
    (hcontinue : ∀ v : V, exponential p₀ v = 1 →
      ∃ (U : Set P) (period : P → V), IsOpen U ∧ p₀ ∈ U ∧
        DifferentiableOn ℂ period U ∧ period p₀ = v ∧ ∀ p ∈ U, exponential p (period p) = 1)
    (Λ : P → Submodule ℤ V) (hΛ : ∀ p v, v ∈ Λ p ↔ exponential p v = 1)
    (identityLocus : Set X) (hclosed : IsClosed identityLocus)
    (hmembership : ∀ p v, embed p (exponential p v) ∈ identityLocus ↔ exponential p v = 1)
    (b₀ : Module.Basis Index ℤ (Λ p₀)) (e₀ : (Index → ℝ) ≃L[ℝ] V)
    (hb₀ : ∀ i, (b₀ i : V) = e₀ (Pi.single i 1)) :
    ∃ (U : Set P) (e : P → (Index → ℝ) ≃L[ℝ] V),
      IsOpen U ∧ p₀ ∈ U ∧ e p₀ = e₀ ∧
      ContinuousOn (fun p => (e p).toContinuousLinearMap) U ∧
      (∀ i, DifferentiableOn ℂ (fun p => e p (Pi.single i 1)) U) ∧
      ∀ p ∈ U, ∃ b : Module.Basis Index ℤ (Λ p),
        ∀ i, (b i : V) = e p (Pi.single i 1) := by
  have hperiod (i : Index) : exponential p₀ (e₀ (Pi.single i 1)) = 1 := by
    apply (hΛ _ _).mp
    rw [← hb₀]
    exact (b₀ i).property
  obtain ⟨U, e, hU, hpU, he₀, he, hhol, hperiods⟩ :=
    exists_holomorphic_real_period_basis_on e₀ (fun i => hcontinue _ (hperiod i))
  have hcentral : ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2), exponential p₀ (e p₀ t) = 1 → t = 0 := by
    intro t ht hker
    rw [he₀] at hker
    exact ArithmeticGeometry.Descent.CMVariety.LatticeCubeBasis.Abelian.integral_basis_fundamental_cube_kernel_free (Λ p₀) b₀ e₀ hb₀ t ht ((hΛ _ _).mpr hker)
  have hcube := H.eventually_fundamental_cube_kernel_free identityLocus hclosed hmembership e
    (he.continuousAt (hU.mem_nhds hpU)) hcentral
  obtain ⟨W, hWsub, hW, hpW⟩ := _root_.mem_nhds_iff.mp hcube
  refine ⟨U ∩ W, e, hU.inter hW, ⟨hpU, hpW⟩, he₀, he.mono inter_subset_left,
    fun i => (hhol i).mono inter_subset_left, ?_⟩
  intro p hp
  exact ArithmeticGeometry.Descent.CMVariety.LatticeCubeBasis.Abelian.exists_integral_basis_of_fundamental_cube (Λ p) (e p)
    (fun i => (hΛ _ _).mpr (hperiods p hp.1 i))
    (fun t ht hmem => hWsub hp.2 t ht ((hΛ _ _).mp hmem))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodBases
