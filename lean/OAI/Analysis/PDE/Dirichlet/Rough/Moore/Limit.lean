import OAI.Analysis.PDE.Dirichlet.VaryingCoefficientLimit
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit
import OAI.LinearAlgebra.Moore.Boundary

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance roughFirstGroup : NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughFirstSpace : NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughSecondGroup : NormedAddCommGroup
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance roughSecondSpace : NormedSpace ℝ
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

theorem quaternionHessianField_lowerHalf {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} (hα : 0 ≤ α)
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (x : D) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD (α / 2) OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα u)) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots u) x := rfl

omit [Fintype ι] in
/-- Varying genuine Moore equations pass to a lower-exponent compact limit,
while the original Hölder exponent, norm and zero-periodic boundary conditions remain intact. -/
theorem exists_moore_dirichlet_solution_of_lowerHalf_limit
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M)
    (A : ℕ → D → Matrix (Fin n) (Fin n) Q)
    (A₀ : D → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 (A₀ x)))
    (F : ℕ → D → ℝ) (F₀ : D → ℝ)
    (hF : ∀ x, Tendsto (fun j ↦ F j x) atTop (𝓝 (F₀ x)))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hΦ : ∀ j, ‖Φ j‖ ≤ M)
    (hmem : ∀ j, Φ j ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (heq : ∀ j x, OAI.LinearAlgebra.Moore.mooreDifferential n (A j x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (Φ j)) x) = F j x)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD (α / 2))
    (hlim : Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ j)) atTop (𝓝 g)) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖u‖ ≤ M ∧
      u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      (∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A₀ x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots u) x) = F₀ x) ∧
      OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα u = g := by
  obtain ⟨u, hu, hug⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.exists_original_exponent_of_lowerHalf_limit hα hM Φ g hΦ hlim
  have hg : g ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.isClosed_latticeDirichlet e lat).mem_of_tendsto hlim
      (Eventually.of_forall (fun j ↦ hmem j))
  have humem : u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat := by
    rw [← hug] at hg
    exact hg
  refine ⟨u, hu, humem, ?_, hug⟩
  intro x
  have hH := quaternionHessianField_tendsto OAI.Analysis.Calculus.Quaternion.fourSlots hlim x
  have hprod := ((OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).tendsto
    (A₀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD (α / 2) OAI.Analysis.Calculus.Quaternion.fourSlots g) x)).comp
    ((hA x).prodMk_nhds hH)
  have heqg : OAI.LinearAlgebra.Moore.mooreDifferential n (A₀ x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD (α / 2) OAI.Analysis.Calculus.Quaternion.fourSlots g) x) = F₀ x := by
    apply tendsto_nhds_unique hprod
    simpa only [Function.comp_def, quaternionHessianField_lowerHalf, heq] using hF x
  simpa only [← hug, quaternionHessianField_lowerHalf] using heqg

omit [Fintype ι] in
theorem exists_moore_dirichlet_solution_of_subsequence
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M)
    (A : ℕ → D → Matrix (Fin n) (Fin n) Q)
    (A₀ : D → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 (A₀ x)))
    (F : ℕ → D → ℝ) (F₀ : D → ℝ)
    (hF : ∀ x, Tendsto (fun j ↦ F j x) atTop (𝓝 (F₀ x)))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hΦ : ∀ j, ‖Φ j‖ ≤ M)
    (hmem : ∀ j, Φ j ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (heq : ∀ j x, OAI.LinearAlgebra.Moore.mooreDifferential n (A j x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (Φ j)) x) = F j x)
    (hcompact : ∃ g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD (α / 2), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ (φ j))) atTop (𝓝 g)) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ M ∧
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A₀ x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F₀ x := by
  obtain ⟨g, φ, hφ, hlim⟩ := hcompact
  obtain ⟨v, hvnorm, hvmem, hveq, _⟩ := exists_moore_dirichlet_solution_of_lowerHalf_limit
    e lat hα hM (fun j ↦ A (φ j)) A₀
    (fun x ↦ (hA x).comp hφ.tendsto_atTop)
    (fun j x ↦ F (φ j) x) F₀ (fun x ↦ (hF x).comp hφ.tendsto_atTop)
    (fun j ↦ Φ (φ j)) (fun j ↦ hΦ (φ j)) (fun j ↦ hmem (φ j))
    (fun j ↦ heq (φ j)) g hlim
  exact ⟨v, hvnorm, hvmem, hveq⟩

theorem exists_moore_dirichlet_solution_of_smooth_approximants [NeZero n]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M)
    (A : ℕ → {x | r x ≤ 0} → Matrix (Fin n) (Fin n) Q)
    (A₀ : {x | r x ≤ 0} → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 (A₀ x)))
    (F : ℕ → CoordinateSpace n 4 → ℝ) (F₀ : {x | r x ≤ 0} → ℝ)
    (hF : ∀ x : {x | r x ≤ 0}, Tendsto (fun j ↦ F j x) atTop (𝓝 (F₀ x)))
    (u : ℕ → CoordinateSpace n 4 → ℝ) (hu : ∀ j, ContDiff ℝ 2 (u j))
    (hup : ∀ j, LatticePeriodic e lat (u j))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hΦ : ∀ j, ‖Φ j‖ ≤ M)
    (hmem : ∀ j, Φ j ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (hv : ∀ j (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ j) x = u j x)
    (hD : ∀ j (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ j) x = fderiv ℝ (u j) x)
    (hDD : ∀ j (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ j) x = fderiv ℝ (fderiv ℝ (u j)) x)
    (heq : ∀ j x, OAI.LinearAlgebra.Moore.mooreDifferential n (A j x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (Φ j)) x) = F j x) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ M ∧
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, OAI.LinearAlgebra.Moore.mooreDifferential n (A₀ x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F₀ x := by
  apply exists_moore_dirichlet_solution_of_subsequence e lat hα.le hM A A₀ hA
    (fun j x ↦ F j x) F₀ hF Φ hΦ hmem heq
  exact exists_closed_banach_subsequence e lat hK hr hrp hbounded hreg
    hα hM u hu hup Φ hΦ hv hD hDD

end OAI.Analysis.PDE.Dirichlet
