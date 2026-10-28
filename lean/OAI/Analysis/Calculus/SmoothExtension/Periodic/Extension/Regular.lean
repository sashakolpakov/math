import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Sublevel
import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sublevel
import OAI.Analysis.PDE.Dirichlet.Moore.GlobalSchauderGeometry

/-! Finite-order periodic extension from a regular closed domain. -/

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.FiniteExtension

variable {m N : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The closed-domain Cᴺ function, not an assumed smooth extension, is
the input. Smooth charts, finite reflection, a partition of unity and
lattice periodization construct the global periodic representative. -/
theorem exists_latticePeriodic_extension_regular_sublevel (hm : 0 < m)
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    (r : EuclideanSpace ℝ (Fin m) → ℝ) (hr : ContDiff ℝ ∞ r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hf : ContDiffOn ℝ N f {x | r x ≤ 0}) :
    ∃ g : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ N g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧ ∀ x, r x ≤ 0 → g x = f x := by
  apply exists_latticePeriodic_contDiff_sublevel_extension_on e b hC hr.continuous
    hrp hbounded N f hfp
  exact OAI.Analysis.Calculus.FiniteExtension.exists_local_extension_regular_sublevel hm r hr hreg f hf

/-- The same extension theorem in arbitrary fixed linear coordinates,
including the four-slot quaternionic coordinates of the Dirichlet problem. -/
theorem exists_latticePeriodic_extension_regular_sublevel_equiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hm : 0 < m) (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    (r : E → ℝ) (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : E → ℝ) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hf : ContDiffOn ℝ N f {x | r x ≤ 0}) :
    ∃ g : E → ℝ, ContDiff ℝ N g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀ x, r x ≤ 0 → g x = f x := by
  obtain ⟨g, hg, hgp, hgf⟩ := exists_latticePeriodic_extension_regular_sublevel hm
    (L.trans e) b hC (r ∘ L) (hr.comp L.contDiff) (hrp.comp_domain_equiv L)
    (OAI.Analysis.PDE.Dirichlet.sublevel_transverse_bound_comp_equiv L e hbounded)
    (OAI.Analysis.PDE.Dirichlet.regular_level_comp_equiv L (hr.differentiable (by simp)) hreg)
    (f ∘ L) (hfp.comp_domain_equiv L) (hf.comp L.contDiff.contDiffOn (fun _ hx => hx))
  refine ⟨g ∘ L.symm, hg.comp L.symm.contDiff, ?_, ?_⟩
  · have he : L.symm.trans (L.trans e) = e := by
      apply ContinuousLinearEquiv.ext
      funext x
      change e (L (L.symm x)) = e x
      rw [L.apply_symm_apply]
    have hp := hgp.comp_domain_equiv L.symm
    rw [he] at hp
    exact hp
  · intro x hx
    have hx' : (r ∘ L) (L.symm x) ≤ 0 := by
      simpa only [Function.comp_apply, L.apply_symm_apply] using hx
    simpa only [Function.comp_apply, L.apply_symm_apply] using hgf (L.symm x) hx'

end OAI.Analysis.Calculus.SmoothExtension
