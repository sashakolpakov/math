import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Continuous periodic data are uniformly bounded on a domain with compact
transverse closure. Continuity only on the closed physical domain suffices. -/
theorem exists_lattice_norm_bound {W : Type*} [SeminormedAddCommGroup W]
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    {f : E → W} (hf : ContinuousOn f {x | r x ≤ 0}) (hfper : LatticePeriodic e lat f) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, r x ≤ 0 → ‖f x‖ ≤ M := by
  let K := latticeSublevelCell e lat C r
  have hK : IsCompact K := isCompact_latticeSublevelCell e lat hC hr
  have hKD : K ⊆ {x | r x ≤ 0} := inter_subset_right
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hf.mono hKD).norm
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro x hx
  have hrep : latticeRepresentative e lat x ∈ K :=
    latticeRepresentative_mem_sublevelCell e lat hrper hbounded hx
  have hm : ‖f (latticeRepresentative e lat x)‖ ≤ M := hM (mem_image_of_mem _ hrep)
  rw [hfper.representative] at hm
  exact hm.trans (by linarith [le_max_left M 0])

theorem exists_lattice_positive_lower
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C) (hne : {x | r x ≤ 0}.Nonempty)
    {f : E → ℝ} (hf : ContinuousOn f {x | r x ≤ 0}) (hfper : LatticePeriodic e lat f)
    (hpos : ∀ x, r x ≤ 0 → 0 < f x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, r x ≤ 0 → m ≤ f x := by
  let K := latticeSublevelCell e lat C r
  have hK : IsCompact K := isCompact_latticeSublevelCell e lat hC hr
  have hKD : K ⊆ {x | r x ≤ 0} := inter_subset_right
  have hrep (x) (hx : r x ≤ 0) : latticeRepresentative e lat x ∈ K :=
    latticeRepresentative_mem_sublevelCell e lat hrper hbounded hx
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, hrep x hx⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne (hf.mono hKD)
  refine ⟨f y, hpos y (hKD hy), ?_⟩
  intro x hx
  have hm : f y ≤ f (latticeRepresentative e lat x) := hmin (hrep x hx)
  rwa [hfper.representative] at hm

theorem exists_lattice_second_derivative_bound
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r f : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hf : ContDiff ℝ 2 f) (hfper : LatticePeriodic e lat f) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M := by
  apply exists_lattice_norm_bound e lat hC hr hrper hbounded
    _ hfper.fderiv.fderiv
  exact ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuous.continuousOn

end OAI.Analysis.PDE.Dirichlet
