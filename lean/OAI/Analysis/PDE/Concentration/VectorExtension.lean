import OAI.Analysis.PDE.Concentration.LocalLatticeExtension
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

/-- The scalar periodic germ-extension construction applies coordinatewise
to every finite-dimensional coefficient field. This includes the Jacobian,
second derivative, and background Hessian fields of the moving-domain PDE. -/
theorem exists_smooth_lattice_vector_extension_near
    {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {U : Set E} (hU : IsOpen U)
    (hCU : ∀ x, (e x).2 ∈ C → x ∈ U)
    (u : E → F) (hu : ContDiffOn ℝ ∞ u U) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀ x, (e x).2 ∈ C → g =ᶠ[𝓝 x] u := by
  let A : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have hc (i : Fin (finrank ℝ F)) : ContDiffOn ℝ ∞ (fun x => A (u x) i) U := by
    let ev : (Fin (finrank ℝ F) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact ev.contDiff.comp_contDiffOn (A.contDiff.comp_contDiffOn hu)
  have hp (i : Fin (finrank ℝ F)) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => A (u x) i) :=
    huper.comp (fun v => A v i)
  choose g hg hgp hgu using fun i =>
    exists_smooth_lattice_extension_near e b hC hU hCU (fun x => A (u x) i) (hc i) (hp i)
  refine ⟨fun x => A.symm (fun i => g i x), A.symm.contDiff.comp (contDiff_pi.mpr hg), ?_, ?_⟩
  · intro x l
    apply congrArg A.symm
    funext i
    exact hgp i x l
  · intro x hx
    have he : ∀ᶠ y in 𝓝 x, ∀ i, g i y = A (u y) i :=
      Filter.eventually_all.mpr (fun i => hgu i x hx)
    filter_upwards [he] with y hy
    exact A.symm_apply_eq.mpr (funext hy)

end OAI.Analysis.PDE.Concentration
