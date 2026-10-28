import OAI.Analysis.PDE.Dirichlet.Maximum

open Set Filter
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A maximum on a compact representative set is a genuine local maximum at
every interior maximizing point. No artificial cell-face boundary condition
is needed. The representative map need not be continuous. -/
theorem localMax_of_compact_representatives {r f : E → ℝ} {K : Set E} (p : E → E)
    (hr : Continuous r) (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    {y : E} (hy : r y < 0) (hmax : IsMaxOn f K y) : IsLocalMax f y := by
  have hnear : ∀ᶠ z in 𝓝 y, r z < 0 := (isOpen_lt hr continuous_const).mem_nhds hy
  filter_upwards [hnear] with z hz
  rw [← hfp z hz.le]
  exact hmax (hrep z hz.le)

theorem strict_maximum_principle_representatives
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {r f : E → ℝ} {K : Set E} {M : ℝ} (p : E → E)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0}) (hr : Continuous r)
    (hf : ContDiff ℝ 2 f) (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (ha : ∀ x, r x < 0 → ∀ i, 0 ≤ a x i)
    (hL : ∀ x, r x < 0 → 0 < ellipticValue a v f x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ hf.continuous.continuousOn
  by_cases hyz : r y = 0
  · rw [← hfp x hx]
    exact (hmax (hrep x hx)).trans (hbd y hyz)
  · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
    have hlocal := localMax_of_compact_representatives p hr hrep hfp hyneg hmax
    have hnonpos := ellipticValue_nonpos_of_localMax (v := v) (ha y hyneg) hf hlocal
    exact False.elim (not_lt_of_ge hnonpos (hL y hyneg))

/-- Weak maximum principle on periodic domains, stated through the exact
compact-representative properties used in the proof. The defining function
supplies the strict barrier and vanishes only on the physical boundary. -/
theorem maximum_principle_representatives
    {ι : Type*} [Fintype ι] {a : E → ι → ℝ} {v : E → ι → E}
    {r f : E → ℝ} {K : Set E} {M : ℝ} (p : E → E)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0})
    (hr : ContDiff ℝ 2 r) (hf : ContDiff ℝ 2 f)
    (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hrp : ∀ x, r x ≤ 0 → r (p x) = r x)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (ha : ∀ x, r x < 0 → ∀ i, 0 ≤ a x i)
    (hL : ∀ x, r x < 0 → 0 ≤ ellipticValue a v f x)
    (hrL : ∀ x, r x < 0 → 0 < ellipticValue a v r x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  intro x hx
  have heps (ε : ℝ) (hε : 0 < ε) : f x + ε * r x ≤ M := by
    apply strict_maximum_principle_representatives (a := a) (v := v) p hK hKD hr.continuous
      (hf.add (hr.const_smul ε)) hrep _ ha _ _ x hx
    · intro z hz
      simp only [hfp z hz, hrp z hz]
    · intro z hz
      rw [ellipticValue_add_smul a v hf hr]
      exact add_pos_of_nonneg_of_pos (hL z hz) (mul_pos hε (hrL z hz))
    · intro z hz
      simpa only [hz, smul_zero, add_zero] using hbd z hz
  have ht : Tendsto (fun ε : ℝ ↦ f x + ε * r x) (𝓝[>] 0) (𝓝 (f x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x + ε * r x) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε ↦ heps ε hε))

end OAI.Analysis.PDE.Dirichlet
