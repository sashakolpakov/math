import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Approximation
import OAI.Analysis.PDE.Dirichlet.Periodic.MooreBarrierBound

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance roughSupFirstGroup : NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughSupFirstSpace : NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughSupSecondGroup : NormedAddCommGroup
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughSupSecondSpace : NormedSpace ℝ
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

/-- The a priori Schauder estimate for genuine global C³ representatives,
still retaining the C⁰ term. This does not assert solvability of any equation,
and does not require an extension theorem for arbitrary rough Hölder jets. -/
def MooreDirichletSchauderSupEstimate
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} (hΩD : Ω ⊆ D) (α : ℝ)
    (A : D → Matrix (Fin n) (Fin n) Q) (C : ℝ) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∀ F : CoordinateSpace n 4 → ℝ,
    (∀ x : D, |F x| ≤ B) →
    (∀ x y : D, |F x - F y| ≤ B * dist x y ^ α) →
    ∀ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat →
      ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u → LatticePeriodic e lat u →
      (∀ x, x ∈ D → x ∉ Ω → u x = 0) →
      (∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x) →
      (∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x) →
      (∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x : D, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F x) →
      ‖v‖ ≤ C * (B + ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value v‖)

omit [Fintype ι] in
/-- A common maximum-principle bound removes the C⁰ term for genuine
smooth representatives, exactly the solutions used before compactness. -/
theorem moore_schauder_bound_of_C0
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r : CoordinateSpace n 4 → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α C B G : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (hest : MooreDirichletSchauderSupEstimate e lat hΩD α (fun x ↦ A x) C)
    (hbound : ∀ u : CoordinateSpace n 4 → ℝ,
      ContDiff ℝ 2 u → LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 → |mooreLinearization A u x| ≤ G) →
      ∀ x, r x ≤ 0 → |u x| ≤ B * G)
    (F : CoordinateSpace n 4 → ℝ)
    (hF : ∀ x : {x | r x ≤ 0}, |F x| ≤ G)
    (hFH : ∀ x y : {x | r x ≤ 0}, |F x - F y| ≤ G * dist x y ^ α)
    (u : CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 3 u)
    (hup : LatticePeriodic e lat u) (hu0 : ∀ x, r x = 0 → u x = 0)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hv : v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (hv0 : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x)
    (hv1 : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x)
    (hv2 : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x)
    (heq : ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F x) :
    ‖v‖ ≤ (C * (1 + B)) * G := by
  have hLu (x : CoordinateSpace n 4) (hx : r x < 0) :
      |mooreLinearization A u x| ≤ G := by
    have hx' := heq ⟨x, hx.le⟩
    rw [quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots v u ⟨x, hx.le⟩
      (hv2 ⟨x, hx.le⟩)] at hx'
    change |OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)| ≤ G
    rw [hx']
    exact hF ⟨x, hx.le⟩
  have hvB : ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value v‖ ≤ B * G :=
    (BoundedContinuousFunction.norm_le (mul_nonneg hB hG)).2 (fun x ↦ by
      simpa only [Real.norm_eq_abs, hv0] using
        hbound u (hu.of_le (by norm_num)) hup hu0 hLu x x.property)
  calc
    ‖v‖ ≤ C * (G + ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value v‖) := hest G hG F hF hFH v hv u hu hup
      (fun x hx hx' ↦ hu0 x (le_antisymm hx (not_lt.mp hx'))) hv0 hv1 hv2 heq
    _ ≤ C * (G + B * G) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hvB) hC
    _ = (C * (1 + B)) * G := by ring

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
/-- Simultaneous approximation with the C⁰ maximum-principle term removed
only for the genuine smooth solutions, before taking the compact limit. -/
theorem exists_rough_moore_solution_of_schauder_and_C0
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α C B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (ψ : ℕ → CoordinateSpace n 4 → ℝ)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) (hψp : ∀ j, LatticePeriodic e lat (ψ j))
    (hpos : ∀ j x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x)).PosDef)
    (A₀ : {x | r x ≤ 0} → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x : {x | r x ≤ 0}, Tendsto
      (fun j ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) atTop (𝓝 (A₀ x)))
    (hestimate : ∀ j, MooreDirichletSchauderSupEstimate e lat hΩD α
      (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) C)
    (hbound : ∀ j G, 0 ≤ G → ∀ u : CoordinateSpace n 4 → ℝ,
      ContDiff ℝ 2 u → LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 → |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j)) u x| ≤ G) →
      ∀ x, r x ≤ 0 → |u x| ≤ B * G)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ (C * (1 + B)) * ‖f‖ ∧
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
  choose u hu hup hu0 v hv D hDp hvD hv0 hv1 hv2 heq using hsol
  have hvnorm (j : ℕ) : ‖v j‖ ≤ (C * (1 + B)) * ‖f‖ :=
    moore_schauder_bound_of_C0 e lat hC hB (norm_nonneg f) _ (hestimate j)
      (hbound j ‖f‖ (norm_nonneg f)) (F j) (fun x ↦ hFB j x) (fun x y ↦ hFH j x y)
      (u j) (hu j) (hup j) (hu0 j) (v j) (hv j) (hv0 j) (hv1 j) (hv2 j) (heq j)
  exact exists_moore_dirichlet_solution_of_smooth_approximants e lat hK
    (hr.of_le (by norm_num)) hrp hbounded hreg hα
    (mul_nonneg (mul_nonneg hC (by linarith)) (norm_nonneg f))
    (fun j x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ j) x) A₀ hA F (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val)
    (fun x ↦ hFlim.tendsto_at x) u (fun j ↦ (hu j).of_le (by norm_num)) hup v hvnorm hv
    hv0 hv1 hv2 heq

end OAI.Analysis.PDE.Dirichlet
