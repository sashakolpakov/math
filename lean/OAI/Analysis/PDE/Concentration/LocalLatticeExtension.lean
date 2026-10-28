import OAI.Analysis.PDE.Concentration.LocalPeriodicExtension
import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def splitLatticeShift (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    Submodule.span ℤ (Set.range b) →+ E where
  toFun z := e.symm (z, 0)
  map_zero' := by simp
  map_add' z w := by
    simp only [Submodule.coe_add, ← map_add, Prod.mk_add_mk, add_zero]

omit [FiniteDimensional ℝ E] in
theorem finite_splitLatticeShift_norm (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (R : ℝ) : {z : Submodule.span ℤ (Set.range b) | ‖splitLatticeShift e b z‖ ≤ R}.Finite := by
  let A : E →L[ℝ] P := (ContinuousLinearMap.fst ℝ P V).comp e.toContinuousLinearMap
  have hf := ZSpan.setFinite_inter b (Metric.isBounded_closedBall (x := (0 : P))
    (r := ‖A‖ * R))
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro z hz
  refine ⟨?_, z.property⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  have hAz : A (splitLatticeShift e b z) = z := by simp [A, splitLatticeShift]
  rw [← hAz]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg A))

/-- Smooth local data on a full periodic cylinder can be extended near any
compact transverse part, preserving the exact lattice and every derivative
there. The extension is constructed separately for each compact part. -/
theorem exists_smooth_lattice_extension_near
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {U : Set E} (hU : IsOpen U)
    (hCU : ∀ x, (e x).2 ∈ C → x ∈ U)
    (u : E → ℝ) (hu : ContDiffOn ℝ ∞ u U) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀ x, (e x).2 ∈ C → g =ᶠ[𝓝 x] u := by
  let K := e.symm '' (parallelepiped b ×ˢ C)
  have hK : IsCompact K := (b.parallelepiped.isCompact.prod hC).image e.symm.continuous
  have hKU : K ⊆ U := by
    rintro x ⟨⟨p, v⟩, hp, rfl⟩
    exact hCU _ (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp.2)
  have hshift (x : E) (z : Submodule.span ℤ (Set.range b)) :
      x + splitLatticeShift e b z = e.symm ((e x).1 + (z : P), (e x).2) := by
    apply e.injective
    simp only [splitLatticeShift, map_add, ContinuousLinearEquiv.apply_symm_apply]
    ext <;> simp
  obtain ⟨g, hg, hgp, hgu⟩ := exists_periodic_extension_near_compact
    (splitLatticeShift e b) (finite_splitLatticeShift_norm e b) hK hU hKU u hu
    (fun x z => by rw [hshift]; exact huper x z)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x z
    rw [← hshift]
    exact hgp x z
  · intro x hx
    apply hgu
    refine ⟨-ZSpan.floor b (e x).1, ?_⟩
    rw [hshift]
    apply mem_image_of_mem
    refine ⟨?_, hx⟩
    simpa only [ZSpan.fract_apply, Submodule.coe_neg, sub_eq_add_neg] using
      ZSpan.fundamentalDomain_subset_parallelepiped b (ZSpan.fract_mem_fundamentalDomain b (e x).1)

end OAI.Analysis.PDE.Concentration
