import OAI.Analysis.PDE.Dirichlet.Periodic.Comparison
import OAI.Analysis.PDE.Dirichlet.DataBarriers

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform scalar barriers for varying bounded positive densities on a periodic domain with compact transverse
closure. Unlike compact-sublevel comparison, no boundary values are imposed
on the faces of a fundamental cell. -/
theorem uniform_solution_barriers_bounded_density_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {B₀ r : CoordinateSpace n 4 → ℝ}
    (hne : {x | r x ≤ 0}.Nonempty)
    (hB₀ : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hBper : LatticePeriodic e lat B₀) (hrper : LatticePeriodic e lat r)
    (hA : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hR : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hzero : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    {m U : ℝ} (hm : 0 < m) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ F : CoordinateSpace n 4 → ℝ,
      (∀ x, r x ≤ 0 → m ≤ F x) → (∀ x, r x ≤ 0 → F x ≤ U) →
      ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 2 u →
      LatticePeriodic e lat u →
      (∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      (∀ x, r x = 0 → u x = 0) →
      ∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x := by
  let K := latticeSublevelCell e lat C r
  have hK : IsCompact K := isCompact_latticeSublevelCell e lat hC hr.continuous
  have hKD : K ⊆ {x | r x ≤ 0} := inter_subset_right
  have hrep (x) (hx : r x ≤ 0) : latticeRepresentative e lat x ∈ K :=
    latticeRepresentative_mem_sublevelCell e lat hrper hbounded hx
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, hrep x hx⟩
  let A := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀
  let R := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r
  have hAc : Continuous A := continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hB₀
  have hRc : Continuous R := continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr
  obtain ⟨B, hB1, hlarge⟩ := exists_uniform_large_moore_barrier hn hK hKne
    A R (fun _ ↦ U) (fun x hx ↦ hA x (hKD hx)) (fun x hx ↦ hR x (hKD hx))
    ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp hRc).continuousOn continuousOn_const
  obtain ⟨b, hb, hb1, hsmall⟩ := exists_uniform_small_moore_barrier hK hKne
    A R (fun _ ↦ m) (fun x hx ↦ hzero x (hKD hx)) continuousOn_const (fun _ _ ↦ hm)
    (continuous_mooreAffineDifferential A R hAc hRc).continuousOn
  have hbB : b ≤ B := hb1.trans hB1
  have hboundsD (x) (hx : r x ≤ 0) :
      OAI.LinearAlgebra.Moore.mooreDet n (A x + b • R x) < m ∧ U < OAI.LinearAlgebra.Moore.mooreDet n (A x + B • R x) := by
    have hsmall' := hsmall _ (hrep x hx)
    have hlarge' := hlarge _ (hrep x hx)
    dsimp only [A, R] at hsmall' hlarge' ⊢
    simpa only [(hBper.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative,
      (hrper.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative] using And.intro hsmall' hlarge'
  refine ⟨b, B, hb, hbB, ?_⟩
  intro F hmin hmax u hu huper husol heq hubd
  have hB : 0 < B := hb.trans_le hbB
  have hlower : ∀ x, r x ≤ 0 → B₀ x + B • r x ≤ B₀ x + u x := by
    apply quaternionic_dirichlet_comparison_lattice hn e lat hC
      (hB₀.add (hr.const_smul B)) (hB₀.add hu) hr hbounded hrper
      (hBper.add (hrper.smul B)) (hBper.add huper) (fun x hx ↦ hR x hx.le)
    · intro x hx
      rw [quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact moore_barrier_matrix_posDef _ _ (hA x hx.le) (hR x hx.le) hB
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hmax x hx.le).trans (hboundsD x hx.le).2.le
    · intro x hx
      simp [hx, hubd x hx]
  have hupper : ∀ x, r x ≤ 0 → B₀ x + u x ≤ B₀ x + b • r x := by
    apply quaternionic_dirichlet_comparison_lattice hn e lat hC
      (hB₀.add hu) (hB₀.add (hr.const_smul b)) hr hbounded hrper
      (hBper.add huper) (hBper.add (hrper.smul b)) (fun x hx ↦ hR x hx.le) husol
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hboundsD x hx.le).1.le.trans (hmin x hx.le)
    · intro x hx
      simp [hx, hubd x hx]
  intro x hx
  constructor
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hlower x hx
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hupper x hx

end OAI.Analysis.PDE.Dirichlet
