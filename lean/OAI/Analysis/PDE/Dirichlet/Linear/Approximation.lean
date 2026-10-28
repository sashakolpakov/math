import OAI.Analysis.PDE.Dirichlet.IndexedHolderApprox
import OAI.Analysis.PDE.Dirichlet.Closed.BanachCompactness
import OAI.Analysis.PDE.Dirichlet.Linear.CompactLimit

open Set Module Filter
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance approximationFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance approximationFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance approximationSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance approximationSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A smooth solution together with its genuine closed-domain jet. This is
only a record of a solution, not a solvability assumption or axiom. -/
structure SmoothLinearDirichletSolution
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {Ω D : Set E}
    (hΩD : Ω ⊆ D) (α M : ℝ)
    (A : D → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ) (F : E → ℝ) where
  u : E → ℝ
  smooth : ContDiff ℝ 2 u
  periodic : LatticePeriodic e lat u
  jet : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α
  bound : ‖jet‖ ≤ M
  dirichlet : jet ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat
  value : ∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.value jet x = u x
  first : ∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative jet x = fderiv ℝ u x
  second : ∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative jet x = fderiv ℝ (fderiv ℝ u) x
  equation : ∀ x : D, A x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative jet x) = F x

/-- Once smooth-data solvability and its uniform Schauder estimate are
proved, arbitrary Hölder data follow without losing the exponent or bound.
The smoothing, compact subsequence, boundary condition and equation limit
are all constructed here rather than required of the smooth-data solver. -/
theorem exists_linear_dirichlet_solution_of_smooth_solutions {m : ℕ}
    (L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (A : {x | r x ≤ 0} → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat)
    (hsolve : ∀ F : E → ℝ, ContDiff ℝ ∞ F → LatticePeriodic e lat F →
      (∀ x, |F x| ≤ ‖f‖) →
      (∀ x y, |F x - F y| ≤ ‖f‖ * dist x y ^ α) →
      Nonempty (SmoothLinearDirichletSolution e lat hΩD α (C * ‖f‖) A F)) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖u‖ ≤ C * ‖f‖ ∧
      u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, A x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u x) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x := by
  have hD : LatticePeriodic e lat (fun x ↦ x ∈ ({x | r x ≤ 0} : Set E)) :=
    hrper.comp (fun t ↦ t ≤ 0)
  obtain ⟨F, hFs, hFp, hFB, hFH, hFlim⟩ :=
    exists_isometric_periodic_smooth_holder_approximation L e lat hD hα hα1 f.val f.property
  let s (j : ℕ) : SmoothLinearDirichletSolution e lat hΩD α (C * ‖f‖) A (F j) :=
    Classical.choice (hsolve (F j) (hFs j) (hFp j) (hFB j) (hFH j))
  have hM : 0 ≤ C * ‖f‖ := mul_nonneg hC (norm_nonneg f)
  obtain ⟨g, φ, hφ, hlim⟩ := exists_closed_banach_subsequence e lat hK hr hrper hbounded hreg
    hα hM (fun j ↦ (s j).u) (fun j ↦ (s j).smooth) (fun j ↦ (s j).periodic)
    (fun j ↦ (s j).jet) (fun j ↦ (s j).bound) (fun j ↦ (s j).value)
    (fun j ↦ (s j).first) (fun j ↦ (s j).second)
  have hFsub (x : {x | r x ≤ 0}) :
      Tendsto (fun j ↦ F (φ j) x) atTop (𝓝 (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x)) :=
    (hFlim.tendsto_at x).comp hφ.tendsto_atTop
  obtain ⟨u, hu, humem, hueq, _⟩ := exists_linear_dirichlet_solution_of_lowerHalf_limit
    e lat hα.le hM A (fun j x ↦ F (φ j) x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val) hFsub
    (fun j ↦ (s (φ j)).jet) (fun j ↦ (s (φ j)).bound)
    (fun j ↦ (s (φ j)).dirichlet) (fun j ↦ (s (φ j)).equation) g hlim
  exact ⟨u, hu, humem, hueq⟩

end OAI.Analysis.PDE.Dirichlet
