import OAI.Analysis.PDE.Dirichlet.Barriers

open Set
open scoped Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Scalar barrier constants chosen uniformly before the unknown solution. -/
theorem uniform_dirichlet_solution_barriers {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K) (hKne : K.Nonempty)
    {B₀ r : CoordinateSpace n 4 → ℝ} (hB₀ : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r)
    (F : CoordinateSpace n 4 → ℝ) (hF : Continuous F)
    (hA : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hR : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hzero : ∀ x ∈ K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hFpos : ∀ x ∈ K, 0 < F x)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 2 u →
      (∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      (∀ x ∈ K, x ∉ interior K → u x = 0) →
      ∀ x ∈ K, B * r x ≤ u x ∧ u x ≤ b * r x := by
  obtain ⟨b, B, hb, hbB, hbounds⟩ := exists_uniform_moore_barriers hn hK hKne
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r) F
    (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hB₀) (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr)
    hF hA hR hzero hFpos
  refine ⟨b, B, hb, hbB, ?_⟩
  intro u hu husol heq hubd
  have hB : 0 < B := hb.trans_le hbB
  have hlower : ∀ x ∈ K, B₀ x + B • r x ≤ B₀ x + u x := by
    apply quaternionic_dirichlet_comparison hn hK (hB₀.add (hr.const_smul B)) (hB₀.add hu)
    · intro x hx
      rw [quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact moore_barrier_matrix_posDef _ _ (hA x (interior_subset hx))
        (hR x (interior_subset hx)) hB
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hbounds x (interior_subset hx)).2.le
    · intro x hx hxi
      simp [hrbd x hx hxi, hubd x hx hxi]
  have hupper : ∀ x ∈ K, B₀ x + u x ≤ B₀ x + b • r x := by
    apply quaternionic_dirichlet_comparison hn hK (hB₀.add hu) (hB₀.add (hr.const_smul b)) husol
    · intro x hx
      rw [heq x hx, quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hr]
      exact (hbounds x (interior_subset hx)).1.le
    · intro x hx hxi
      simp [hrbd x hx hxi, hubd x hx hxi]
  intro x hx
  constructor
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hlower x hx
  · simpa only [smul_eq_mul, add_le_add_iff_left] using hupper x hx

end OAI.Analysis.PDE.Dirichlet
