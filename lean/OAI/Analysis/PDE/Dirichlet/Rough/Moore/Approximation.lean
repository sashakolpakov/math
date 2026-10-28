import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Limit
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothMooreJetExistence

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance roughApproxFirstGroup : NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughApproxFirstSpace : NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughApproxSecondGroup : NormedAddCommGroup
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughApproxSecondSpace : NormedSpace ℝ
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

/-- Only the uniform a priori estimate, with no existence assumption.
The equation uses the actual closed-domain quaternionic Hessian jet. -/
def MooreDirichletSchauderEstimate
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} (hΩD : Ω ⊆ D) (α : ℝ)
    (A : D → Matrix (Fin n) (Fin n) Q) (C : ℝ) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∀ F : CoordinateSpace n 4 → ℝ,
    (∀ x : D, |F x| ≤ B) →
    (∀ x y : D, |F x - F y| ≤ B * dist x y ^ α) →
    ∀ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat →
      (∀ x : D, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F x) →
      ‖v‖ ≤ C * B

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
/-- Arbitrary Hölder forcing and varying smooth positive potentials may be
approximated simultaneously. Smooth solvability is proved elsewhere; the only
analytic premise here is a common Schauder bound. -/
theorem exists_rough_moore_solution_of_positive_smooth_approximants
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (ψ : ℕ → CoordinateSpace n 4 → ℝ)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) (hψp : ∀ j, LatticePeriodic e lat (ψ j))
    (hpos : ∀ j x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x)).PosDef)
    (A₀ : {x | r x ≤ 0} → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x : {x | r x ≤ 0}, Tendsto
      (fun j ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) atTop (𝓝 (A₀ x)))
    (hestimate : ∀ j, MooreDirichletSchauderEstimate e lat hΩD α
      (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) C)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ C * ‖f‖ ∧
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A₀ x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x := by
  let : NeZero n := ⟨by omega⟩
  have hD : LatticePeriodic e lat (fun x ↦ x ∈ ({x | r x ≤ 0} : Set (CoordinateSpace n 4))) :=
    hrp.comp (fun t ↦ t ≤ 0)
  obtain ⟨F, hFs, hFp, hFB, hFH, hFlim⟩ :=
    exists_fourSlot_periodic_smooth_holder_approximation e lat hD hα hα1 f.val f.property
  have hsol (j : ℕ) := exists_smooth_moore_dirichlet_C2Holder_solution hn e lat hK
    hr hrp hbounded hreg (hψ j) (hψp j) (hpos j) (hFs j) (hFp j) (hΩD := hΩD) hα.le hα1
  choose u hu hup hu0 v hv B hB hvB hv0 hv1 hv2 heq using hsol
  have hvnorm (j : ℕ) : ‖v j‖ ≤ C * ‖f‖ := by
    exact hestimate j ‖f‖ (norm_nonneg f) (F j) (fun x ↦ hFB j x)
      (fun x y ↦ hFH j x y) (v j) (hv j) (heq j)
  exact exists_moore_dirichlet_solution_of_smooth_approximants e lat hK
    (hr.of_le (by norm_num)) hrp hbounded hreg hα (mul_nonneg hC (norm_nonneg f))
    (fun j x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) A₀ hA F (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val)
    (fun x ↦ hFlim.tendsto_at x) u (fun j ↦ (hu j).of_le (by norm_num)) hup v hvnorm hv
    hv0 hv1 hv2 heq

end OAI.Analysis.PDE.Dirichlet
