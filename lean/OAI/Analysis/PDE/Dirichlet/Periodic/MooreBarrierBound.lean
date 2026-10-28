import OAI.Analysis.PDE.Dirichlet.Periodic.MooreBarrier

open Set Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- A common positive defining-function barrier gives a common C⁰ inverse
bound, independent of the coefficient field and the particular solution. -/
theorem periodic_moore_C0_bound_of_barrier
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧
      ∀ A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ),
      (∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef) →
      (∀ x, r x < 0 → c ≤ mooreLinearization A r x) →
      ∀ G : ℝ, 0 ≤ G → ∀ f : CoordinateSpace n 4 → ℝ,
      ContDiff ℝ 2 f → LatticePeriodic e lat f →
      (∀ x, r x = 0 → f x = 0) →
      (∀ x, r x < 0 → |mooreLinearization A f x| ≤ G) →
      ∀ x, r x ≤ 0 → |f x| ≤ B * G := by
  obtain ⟨R, hR, hRb⟩ := exists_lattice_norm_bound e lat hK hr.continuous hrp hbounded
    hr.continuous.continuousOn hrp
  refine ⟨R/c, div_pos hR hc, ?_⟩
  intro A hA hAr G hG f hf hfp hf0 hLf x hx
  have hbound := moore_linearized_barrier_estimate_lattice e lat hK hr hf hrp hfp
    hbounded hA (B := 0) (c := G/c) (fun y hy ↦ ?_)
    (fun y hy ↦ hc.trans_le (hAr y hy)) (fun y hy ↦ by simp [hf0 y hy]) x hx
  · calc
      |f x| ≤ 0 - (G/c) * r x := hbound
      _ = (G/c) * (-r x) := by ring
      _ ≤ (G/c) * R := mul_le_mul_of_nonneg_left
        ((neg_le_abs (r x)).trans (hRb x hx)) (div_nonneg hG hc.le)
      _ = (R/c)*G := by ring
  · calc
      |mooreLinearization A f y| ≤ G := hLf y hy
      _ = (G/c)*c := (div_mul_cancel₀ G hc.ne').symm
      _ ≤ (G/c)*mooreLinearization A r y :=
        mul_le_mul_of_nonneg_left (hAr y hy) (div_nonneg hG hc.le)

/-- For any convergent family of the actual cofactor matrices, one tail
has a uniform C⁰ inverse bound. Positivity is required only for the family
members to which the maximum principle is applied. -/
theorem eventually_periodic_moore_C0_bound
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r ψ : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e lat ψ)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (u : ℕ → CoordinateSpace n 4 → ℝ)
    (hc : TendstoUniformlyOn (fun j x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
      (fun x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) atTop {x | r x ≤ 0}) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      (∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)).PosDef) →
      ∀ G : ℝ, 0 ≤ G → ∀ f : CoordinateSpace n 4 → ℝ,
      ContDiff ℝ 2 f → LatticePeriodic e lat f →
      (∀ x, r x = 0 → f x = 0) →
      (∀ x, r x < 0 → |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j)) f x| ≤ G) →
      ∀ x, r x ≤ 0 → |f x| ≤ B * G := by
  obtain ⟨c, hcc, N, hN⟩ := eventually_periodic_moore_defining_lower hn e lat hK hr hrp
    hbounded hψ hψp hrpos hψpos u hc
  obtain ⟨B, hB, hBd⟩ := periodic_moore_C0_bound_of_barrier e lat hK hr hrp hbounded hcc
  exact ⟨B, hB, N, fun j hj hpos ↦ hBd _ hpos (fun x hx ↦ hN j hj x hx.le)⟩

end OAI.Analysis.PDE.Dirichlet
