import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus
import OAI.Analysis.PDE.Dirichlet.Linearized
import OAI.Analysis.PDE.Dirichlet.Estimates

open Filter Set Module
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem moore_strict_maximum_principle_representatives {n : ℕ}
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)} {M : ℝ}
    (p : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0}) (hr : Continuous r)
    (hf : ContDiff ℝ 2 f) (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → 0 < mooreLinearization A f x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ hf.continuous.continuousOn
  by_cases hyz : r y = 0
  · rw [← hfp x hx]
    exact (hmax (hrep x hx)).trans (hbd y hyz)
  · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
    have hlocal := localMax_of_compact_representatives p hr hrep hfp hyneg hmax
    obtain ⟨C, hAC, hCA⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef (A y) (hA y hyneg)
    have hnonpos := mooreLinearization_nonpos_of_localMax C (hA y hyneg) hAC hCA
      (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef (A y) (hA y hyneg)).le hf hlocal
    exact False.elim (not_lt_of_ge hnonpos (hL y hyneg))

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem moore_maximum_principle_lattice {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {M : ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiff ℝ 2 f)
    (hrper : LatticePeriodic e lat r) (hfper : LatticePeriodic e lat f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → 0 ≤ mooreLinearization A f x)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  intro x hx
  have heps (ε : ℝ) (hε : 0 < ε) : f x + ε * r x ≤ M := by
    apply moore_strict_maximum_principle_representatives (A := A)
      (latticeRepresentative e lat)
      (isCompact_latticeSublevelCell e lat hC hr.continuous) inter_subset_right hr.continuous
      (hf.add (hr.const_smul ε))
      (fun z hz ↦ latticeRepresentative_mem_sublevelCell e lat hrper hbounded hz)
      (fun z _ ↦ (hfper.add (hrper.smul ε)).representative z) hA _ _ x hx
    · intro z hz
      rw [mooreLinearization_add_smul A hf hr]
      exact add_pos_of_nonneg_of_pos (hL z hz) (mul_pos hε (hrL z hz))
    · intro z hz
      simpa only [hz, smul_zero, add_zero] using hbd z hz
  have ht : Tendsto (fun ε : ℝ ↦ f x + ε * r x) (𝓝[>] 0) (𝓝 (f x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x + ε * r x) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε ↦ heps ε hε))

theorem moore_linearized_upper_estimate_lattice {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {B c : ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiff ℝ 2 f)
    (hrper : LatticePeriodic e lat r) (hfper : LatticePeriodic e lat f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → 0 ≤ mooreLinearization A f x + c * mooreLinearization A r x)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    (hbd : ∀ x, r x = 0 → f x ≤ B) :
    ∀ x, r x ≤ 0 → f x ≤ B - c * r x := by
  have hbound := moore_maximum_principle_lattice e lat hC hr (hf.add (hr.const_smul c))
    hrper (hfper.add (hrper.smul c)) hbounded hA
    (fun x hx ↦ by rw [mooreLinearization_add_smul A hf hr]; exact hL x hx) hrL
    (fun x hx ↦ by simpa only [hx, smul_zero, add_zero] using hbd x hx)
  intro x hx
  have h := hbound x hx
  change f x + c * r x ≤ B at h
  linarith

theorem moore_linearized_barrier_estimate_lattice {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {r f : CoordinateSpace n 4 → ℝ} {B c : ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiff ℝ 2 f)
    (hrper : LatticePeriodic e lat r) (hfper : LatticePeriodic e lat f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hL : ∀ x, r x < 0 → |mooreLinearization A f x| ≤ c * mooreLinearization A r x)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    (hbd : ∀ x, r x = 0 → |f x| ≤ B) :
    ∀ x, r x ≤ 0 → |f x| ≤ B - c * r x := by
  have hp := moore_linearized_upper_estimate_lattice e lat hC hr hf hrper hfper hbounded hA
    (fun x hx ↦ by have := (abs_le.mp (hL x hx)).1; linarith) hrL
    (fun x hx ↦ (le_abs_self _).trans (hbd x hx))
  have hm := moore_linearized_upper_estimate_lattice e lat hC hr (hf.const_smul (-1 : ℝ))
    hrper (hfper.smul (-1)) hbounded hA
    (fun x hx ↦ by
      rw [mooreLinearization_smul A hf]
      have := (abs_le.mp (hL x hx)).2
      linarith) hrL
    (fun x hx ↦ by simpa using (neg_le_abs _).trans (hbd x hx))
  intro x hx
  have hp' := hp x hx
  have hm' := hm x hx
  change -1 * f x ≤ B - c * r x at hm'
  exact abs_le.mpr ⟨by linarith, hp'⟩

end OAI.Analysis.PDE.Dirichlet
