import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Filter Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def latticeShiftHom (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    Submodule.span ℤ (Set.range b) →+ E where
  toFun l := e.symm ((l : P),0)
  map_zero' := by simp
  map_add' l m := by
    change e.symm ((l : P) + (m : P),0) = _
    rw [← map_add]
    simp

omit [FiniteDimensional ℝ E] in
theorem finite_latticeShiftHom_norm (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (R : ℝ) :
    {z | ‖latticeShiftHom e b z‖ ≤ R}.Finite := by
  let : FiniteDimensional ℝ P := b.finiteDimensional_of_finite
  have hf := ZSpan.setFinite_inter b (Metric.isBounded_closedBall
    (x := (0 : P)) (r := ‖e.toContinuousLinearMap‖ * R))
  have hsub : (fun z : Submodule.span ℤ (Set.range b) ↦ (z : P)) ''
      {z | ‖latticeShiftHom e b z‖ ≤ R} ⊆
      Metric.closedBall (0 : P) (‖e.toContinuousLinearMap‖ * R) ∩ Submodule.span ℤ (Set.range b) := by
    rintro y ⟨z,hz,rfl⟩
    refine ⟨?_,z.property⟩
    simp only [Metric.mem_closedBall,dist_zero_right]
    have h0 : ‖(z : P)‖ ≤ ‖e (latticeShiftHom e b z)‖ := by
      simp [latticeShiftHom]
    exact h0.trans ((e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
  exact (hf.subset hsub).of_finite_image Subtype.val_injective.injOn

theorem exists_latticePeriodic_contDiff_extension_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K C : Set E} (hK : IsClosed K) (hC : IsCompact C)
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    (hrep : ∀x ∈ K, OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x ∈ C)
    (q : ℕ) (u : E → ℝ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hl : ∀x ∈ K, ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → ℝ, ContDiff ℝ q g ∧ ∀y ∈ K ∩ U, g y = u y) :
    ∃g : E → ℝ, ContDiff ℝ q g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧ ∀x ∈ K, g x = u x := by
  have hshift (x : E) (z : Submodule.span ℤ (Set.range b)) :
      x + latticeShiftHom e b z = e.symm ((e x).1 + (z : P),(e x).2) := by
    change x + e.symm ((z : P),0) = _
    simpa only [add_comm] using
      (OAI.Analysis.PDE.Dirichlet.lattice_translate_eq e x (z : P)).symm
  have hcover : ∀x ∈ K, ∃z, x + latticeShiftHom e b z ∈ C := by
    intro x hx
    refine ⟨-ZSpan.floor b (e x).1,?_⟩
    rw [hshift]
    simpa only [OAI.Analysis.PDE.Dirichlet.latticeRepresentative,ZSpan.fract_apply,Submodule.coe_neg,sub_eq_add_neg]
      using hrep x hx
  obtain ⟨g,hg,hgp,hgK⟩ := exists_periodic_contDiff_extension_of_local
    (latticeShiftHom e b) (finite_latticeShiftHom_norm e b) hK hC
    (fun x hx z ↦ by rw [hshift]; exact Eq.mpr (hKper x z) hx)
    hcover q u (fun x _ z ↦ by rw [hshift]; exact huper x z) hl
  refine ⟨g,hg,?_,hgK⟩
  intro x z
  rw [← hshift]
  exact hgp x z

end OAI.Analysis.Calculus.SmoothExtension
