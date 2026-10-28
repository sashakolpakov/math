import OAI.Analysis.PDE.Dirichlet.Linear.Local

open Set Filter Module
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Strict maximum principle for an interior-classical solution continuous
up to the physical boundary, with compact periodic representatives. -/
theorem moore_strict_maximum_continuous_representatives {n : ℕ}
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M : ℝ}
    (p : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0}) (hr : Continuous r)
    (hf : ContDiffOn ℝ 2 f {x | r x < 0})
    (hfc : ContinuousOn f {x | r x ≤ 0})
    (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → 0 < mooreLinearization A f x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ (hfc.mono hKD)
  by_cases hyz : r y = 0
  · rw [← hfp x hx]
    exact (hmax (hrep x hx)).trans (hbd y hyz)
  · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
    have hlocal := localMax_of_compact_representatives p hr hrep hfp hyneg hmax
    have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
    have hnonpos := mooreLinearization_nonpos_of_localMax_at (hA y hyneg)
      (hf.contDiffAt (hΩ.mem_nhds hyneg)) hlocal
    exact False.elim (not_lt_of_ge hnonpos (hL y hyneg))

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem moore_maximum_continuous_lattice {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {M : ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiffOn ℝ 2 f {x | r x < 0})
    (hfc : ContinuousOn f {x | r x ≤ 0})
    (hrper : LatticePeriodic e lat r) (hfper : LatticePeriodic e lat f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → 0 ≤ mooreLinearization A f x)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  intro x hx
  have heps (ε : ℝ) (hε : 0 < ε) : f x + ε * r x ≤ M := by
    apply moore_strict_maximum_continuous_representatives (A := A)
      (latticeRepresentative e lat)
      (isCompact_latticeSublevelCell e lat hC hr.continuous) inter_subset_right hr.continuous
      (hf.add (hr.contDiffOn.const_smul ε))
      (hfc.add (hr.continuous.continuousOn.const_smul ε))
      (fun z hz ↦ latticeRepresentative_mem_sublevelCell e lat hrper hbounded hz)
      (fun z _ ↦ (hfper.add (hrper.smul ε)).representative z) hA _ _ x hx
    · intro z hz
      rw [mooreLinearization_add_smul_at A (hf.contDiffAt (hΩ.mem_nhds hz)) hr.contDiffAt]
      exact add_pos_of_nonneg_of_pos (hL z hz) (mul_pos hε (hrL z hz))
    · intro z hz
      simpa only [hz, smul_zero, add_zero] using hbd z hz
  have ht : Tendsto (fun ε : ℝ ↦ f x + ε * r x) (𝓝[>] 0) (𝓝 (f x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x + ε * r x) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (Eventually.mono self_mem_nhdsWithin (fun ε hε ↦ heps ε hε))

theorem moore_linearized_zero_continuous_lattice {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiffOn ℝ 2 f {x | r x < 0})
    (hfc : ContinuousOn f {x | r x ≤ 0})
    (hrper : LatticePeriodic e lat r) (hfper : LatticePeriodic e lat f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → mooreLinearization A f x = 0)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    (hbd : ∀ x, r x = 0 → f x = 0) : ∀ x, r x ≤ 0 → f x = 0 := by
  have hp := moore_maximum_continuous_lattice e lat hC hr hf hfc hrper hfper hbounded hA
    (fun x hx ↦ (hL x hx).ge) hrL (fun x hx ↦ (hbd x hx).le)
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hm := moore_maximum_continuous_lattice (M := 0) e lat hC hr (hf.const_smul (-1 : ℝ))
    (hfc.const_smul (-1 : ℝ)) hrper (hfper.smul (-1)) hbounded hA
    (by
      intro x hx
      rw [mooreLinearization_smul_at A (hf.contDiffAt (hΩ.mem_nhds hx)), hL x hx]
      simp)
    hrL (by intro x hx; simp only [hbd x hx, smul_zero, le_refl])
  intro x hx
  have h₁ := hp x hx
  have h₂ := hm x hx
  change -1 * f x ≤ 0 at h₂
  linarith

end OAI.Analysis.PDE.Dirichlet
