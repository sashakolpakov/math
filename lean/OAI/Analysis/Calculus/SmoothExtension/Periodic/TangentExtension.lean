import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentPeriodization

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E F T : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup T]

/-- A smooth local section of a periodic kernel constraint can be extended
periodically without changing its germ. Compact cutoff and discrete translates
preserve the pointwise linear constraint. -/
theorem exists_periodic_kernel_extension
    (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    (S : Set E) (hS : ∀ x ∈ S, ∀ z : T, x + L z ∈ S)
    (A : E → F →L[ℝ] ℝ) (hAp : ∀ x z, A (x + L z) = A x)
    {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U)
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hAf : ∀ x ∈ U ∩ S, A x (f x) = 0) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧
      (∀ x z, g (x + L z) = g x) ∧ (∀ x ∈ S, A x (g x) = 0) ∧
      ∃ O : Set E, IsOpen O ∧ a ∈ O ∧ O ⊆ U ∧ EqOn g f O := by
  obtain ⟨d, hd, hgap⟩ := exists_positive_period_gap L hLi hL
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let R : ℝ := min (ε/2) (d/4)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRε : R < ε := (min_le_left _ _).trans_lt (by linarith)
  have hRd : R ≤ d/4 := min_le_right _ _
  let b : ContDiffBump a := ⟨R/2, R, by positivity, by linarith⟩
  let φ : E → F := fun x ↦ b x • f x
  have hφ : ContDiff ℝ ∞ φ := b.contDiff.smul hf
  have hφzero (x : E) (hx : R ≤ dist x a) : φ x = 0 := by
    simp only [φ, b.zero_of_le_dist hx, zero_smul]
  have hφc : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a R)
    intro x hx
    exact hφzero x (le_of_not_ge hx)
  have hφA (x : E) (hx : x ∈ S) : A x (φ x) = 0 := by
    by_cases hdist : dist x a < R
    · have hxU : x ∈ U := hεU (hdist.trans hRε)
      simp only [φ, map_smul, hAf x ⟨hxU, hx⟩, smul_zero]
    · rw [hφzero x (le_of_not_gt hdist), map_zero]
  refine ⟨vectorPeriodization L φ, contDiff_vectorPeriodization L hL hφ hφc,
    fun x z ↦ vectorPeriodization_add L φ z x, ?_, ball a (R/2), isOpen_ball,
    mem_ball_self (by positivity), ?_, ?_⟩
  · intro x hx
    apply continuousLinearMap_vectorPeriodization_eq_zero L hL hφc (A x) x
    intro z
    rw [← hAp x z]
    exact hφA (x + L z) (hS x hx z)
  · intro x hx
    apply hεU
    change dist x a < ε
    have hxR : dist x a < R/2 := hx
    linarith
  · intro x hx
    have hself : φ x = f x := by
      change b x • f x = f x
      rw [b.one_of_mem_closedBall (show dist x a ≤ R/2 from le_of_lt hx), one_smul]
    rw [← hself]
    apply vectorPeriodization_eq_self
    intro z hz
    apply hφzero
    have htriangle : ‖L z‖ ≤ dist (x + L z) a + dist x a := by
      have ht := dist_triangle (x + L z) a x
      simpa only [dist_eq_norm, add_sub_cancel_left, norm_sub_rev] using ht
    have hzlower := hgap z hz
    have hxR : dist x a < R/2 := hx
    linarith

variable {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_latticePeriodic_tangent_extension
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r : E → ℝ) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U)
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (htan : ∀ x ∈ U, r x = 0 → fderiv ℝ r x (f x) = 0) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat g ∧
      (∀ x, r x = 0 → fderiv ℝ r x (g x) = 0) ∧
      ∃ O : Set E, IsOpen O ∧ a ∈ O ∧ O ⊆ U ∧ EqOn g f O := by
  let L := latticeShiftHom e lat
  have hshift (x : E) (z : Submodule.span ℤ (Set.range lat)) :
      x + L z = e.symm ((e x).1 + (z : P), (e x).2) := by
    change x + e.symm ((z : P), 0) = _
    simpa only [add_comm] using (OAI.Analysis.PDE.Dirichlet.lattice_translate_eq e x (z : P)).symm
  have hLi : Function.Injective L := by
    intro z w h
    apply Subtype.ext
    have he := congrArg (fun x : E ↦ (e x).1) h
    simpa only [L, latticeShiftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply] using he
  obtain ⟨g, hg, hgp, hgt, hlocal⟩ := exists_periodic_kernel_extension L hLi
    (finite_latticeShiftHom_norm e lat) {x | r x = 0}
    (by
      intro x hx z
      change r (x + L z) = 0
      rw [hshift, hrp x z]
      exact hx)
    (fderiv ℝ r) (by intro x z; rw [hshift]; exact hrp.fderiv x z)
    hU ha f hf (fun x hx ↦ htan x hx.1 hx.2)
  refine ⟨g, hg, ?_, hgt, hlocal⟩
  intro x z
  rw [← hshift]
  exact hgp x z

end OAI.Analysis.Calculus.SmoothExtension
