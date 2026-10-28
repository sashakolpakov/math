import OAI.Analysis.Calculus.Coefficients.Positive

open Set Filter Module Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

variable {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Divergence-preserving approximation for the actual Dirichlet
linearization. The potential is mollified, not the matrix entries.
The ellipticity neighborhood and all closed-domain Hölder bounds are
independent of the approximation index. -/
theorem exists_periodic_elliptic_cofactor_approximation
    (hn : 1 ≤ n) (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hf : ContDiff ℝ 3 f) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ u : ℕ → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ, ∃ O : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ∃ lam C : ℝ,
      IsOpen O ∧ {x | r x ≤ 0} ⊆ O ∧ 0 < lam ∧ 0 < C ∧
      (∀ j, ContDiff ℝ ∞ (u j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j)) ∧
      (∀ j x q, (∑ p, fderiv ℝ (fun y ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0) ∧
      (∀ j x, x ∈ O → ∀ v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4,
        lam*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) v)) ∧
      (∀ j x, r x ≤ 0 → ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
      (∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
          OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) ∧
      (∀ j x, r x ≤ 0 → ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
      (∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
          OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) ∧
      TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
        (fun x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop {x | r x ≤ 0} ∧
      TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
        (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop {x | r x ≤ 0} := by
  obtain ⟨u,hu,hup,_,hmp,hdiv,hdata⟩ := exists_periodic_smooth_cofactor_approximation e b f hf hfp hα hα1
  let a := fun j x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)
  let A := fun x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)
  have hap j : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (a j) := ((hup j).quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp OAI.Analysis.PDE.Dirichlet.detRealOperator
  have hAp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b A := (hfp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp OAI.Analysis.PDE.Dirichlet.detRealOperator
  have hAc : Continuous A :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1).continuous.comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hf).continuous
  let S := OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r
  have hS : IsCompact S := OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr
  obtain ⟨lam,hlam,hell⟩ := compact_positive_cofactor_lower hn hS f hf
    (fun x hx ↦ hpos x hx.2)
  obtain ⟨O,hO,hDO,N,hN⟩ := periodic_elliptic_neighborhood e b A hAc a hap hS
    (fun x hx ↦ OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrp hbounded hx)
    (hdata (cthickening 1 S) hS.cthickening).2.1 hlam hell
  obtain ⟨C,hC,hCB,hCH⟩ := periodic_global_bound_holder_of_compact_bounds e b hK hr hrp hbounded a hap hα (by
    intro T hT
    obtain ⟨_,_,B,hB,_,hB₀,_,hBH⟩ := hdata T hT
    exact ⟨B,hB,hB₀,hBH⟩)
  obtain ⟨M,hM,hMB,hMH⟩ := periodic_global_bound_holder_of_compact_bounds e b hK hr hrp hbounded
    (fun j x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)) hmp hα (by
      intro T hT
      obtain ⟨_,_,B,hB,hB₀,_,hBH,_⟩ := hdata T hT
      exact ⟨B,hB,hB₀,hBH⟩)
  have hcA := periodic_tendstoUniformlyOn_sublevel e b hrp hbounded a A hap hAp (hdata S hS).2.1
  have hcM := periodic_tendstoUniformlyOn_sublevel e b hrp hbounded
    (fun j x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
    (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) hmp
    ((hfp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp OAI.Analysis.PDE.Dirichlet.mooreRealMatrix) (hdata S hS).1
  refine ⟨fun j ↦ u (N+j),O,lam/2,C+M,hO,hDO,by positivity,by positivity,
    fun j ↦ hu (N+j),fun j ↦ hup (N+j),fun j ↦ hdiv (N+j),?_,?_,?_,?_,?_,
    tendstoUniformlyOn_nat_add hcA N,tendstoUniformlyOn_nat_add hcM N⟩
  · intro j x hx v
    exact hN (N+j) (by omega) x hx v
  · intro j x hx
    exact (hCB (N+j) x hx).trans (by linarith)
  · intro j x hx y hy
    exact (hCH (N+j) x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))
  · intro j x hx
    exact (hMB (N+j) x hx).trans (by linarith)
  · intro j x hx y hy
    exact (hMH (N+j) x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))

end OAI.Analysis.Calculus.Coefficients
