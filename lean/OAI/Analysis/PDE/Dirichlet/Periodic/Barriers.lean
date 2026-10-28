import OAI.Analysis.PDE.Dirichlet.Periodic.Comparison
import OAI.Analysis.PDE.Dirichlet.DataBarriers

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Data-only scalar barriers on a periodic domain with compact transverse
closure. Unlike compact-sublevel comparison, no boundary values are imposed
on the faces of a fundamental cell. -/
theorem uniform_dirichlet_solution_barriers_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {B₀ r : CoordinateSpace n 4 → ℝ}
    (hne : {x | r x ≤ 0}.Nonempty)
    (hB₀ : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r)
    (F : CoordinateSpace n 4 → ℝ) (hF : Continuous F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hBper : LatticePeriodic e lat B₀) (hrper : LatticePeriodic e lat r)
    (hFper : LatticePeriodic e lat F)
    (hA : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hR : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hzero : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 2 u →
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
  obtain ⟨b, B, hb, hbB, hbounds⟩ := exists_uniform_moore_barriers hn hK hKne
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r) F
    (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hB₀) (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr)
    hF (fun x hx ↦ hA x (hKD hx)) (fun x hx ↦ hR x (hKD hx))
    (fun x hx ↦ hzero x (hKD hx)) (fun x hx ↦ hFpos x (hKD hx))
  have hboundsD (x) (hx : r x ≤ 0) := hbounds _ (hrep x hx)
  simp only [(hBper.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative,
    (hrper.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative, hFper.representative] at hboundsD
  refine ⟨b, B, hb, hbB, ?_⟩
  intro u hu huper husol heq hubd
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
      exact (hboundsD x hx.le).2.le
    · intro x hx
      simp [hx, hubd x hx]
  have hupper : ∀ x, r x ≤ 0 → B₀ x + u x ≤ B₀ x + b • r x := by
    apply quaternionic_dirichlet_comparison_lattice hn e lat hC
      (hB₀.add hu) (hB₀.add (hr.const_smul b)) hr hbounded hrper
      (hBper.add huper) (hBper.add (hrper.smul b)) (fun x hx ↦ hR x hx.le) husol
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hboundsD x hx.le).1.le
    · intro x hx
      simp [hx, hubd x hx]
  intro x hx
  constructor
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hlower x hx
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hupper x hx

end OAI.Analysis.PDE.Dirichlet
