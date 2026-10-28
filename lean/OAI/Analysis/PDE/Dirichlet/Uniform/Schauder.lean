import OAI.Analysis.PDE.Dirichlet.SchauderData
import OAI.Analysis.PDE.Dirichlet.Periodic.SchauderFamily

open Set Module InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- One global Schauder constant for every admissible coefficient field,
right side, and smooth solution on a fixed periodic regular sublevel. -/
theorem uniform_periodic_schauder_data (hm : 3 ≤ m)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    (r : E → ℝ) (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {α ell Λ N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ d : PeriodicSchauderData e b r hΩD α ell Λ N,
      ‖d.jets‖ ≤ C*(d.forcingBound+‖OAI.Analysis.Normed.Function.Holder.C2Holder.value d.jets‖) := by
  let I := PeriodicSchauderData e b r hΩD α ell Λ N
  exact periodic_schauder_family hm e b hK r hr hrp hbounded hreg
    hα hα1 hell hΛ hN
    (fun d : I => d.coefficient) (fun d => d.coefficient_continuous)
    (fun d => d.coefficient_symmetric) (fun d => d.elliptic_lower)
    (fun d => d.elliptic_upper) (fun d => d.coefficient_norm) (fun d => d.coefficient_holder)
    (fun d => d.solution) (fun d => d.solution_smooth) (fun d => d.solution_periodic)
    (fun d => d.solution_zero) (fun d => d.forcing) (fun d => d.forcingBound)
    (fun d => ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value d.jets‖) (fun d => d.forcingBound_nonneg)
    (fun d => norm_nonneg _) (fun d => d.forcing_norm) (fun d => d.forcing_holder)
    (fun d => d.solution_bound) (fun d => d.equation) (fun d => d.jets)
    (fun d => d.jets_value) (fun d => d.jets_first) (fun d => d.jets_second)

/-- Expanded form of the uniform global estimate. Only the C⁰ norm of
the solution remains on the right; no assumed local estimate, extension,
inverse, or regularity theorem is part of the hypotheses. -/
theorem uniform_periodic_schauder (hm : 3 ≤ m)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    (r : E → ℝ) (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {α ell Λ N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ A : E → E →L[ℝ] E, Continuous A →
      (∀ x, r x ≤ 0 → (A x).toLinearMap.IsSymmetric) →
      (∀ x, r x ≤ 0 → ∀ v : E, ell*‖v‖^2 ≤ inner ℝ v (A x v)) →
      (∀ x, r x ≤ 0 → ∀ v : E, inner ℝ v (A x v) ≤ Λ*‖v‖^2) →
      (∀ x, r x ≤ 0 → ‖A x‖ ≤ N) →
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 → ‖A x-A y‖ ≤ N*dist x y^α) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u → LatticePeriodic e b u →
      (∀ x, r x = 0 → u x = 0) →
      ∀ (F : E → ℝ) (B : ℝ), 0 ≤ B →
      (∀ x, r x ≤ 0 → |F x| ≤ B) →
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 → |F x-F y| ≤ B*dist x y^α) →
      (∀ x, r x ≤ 0 → OAI.Analysis.PDE.Elliptic.ellipticTrace A u x = F x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ‖U‖ ≤ C*(B+‖OAI.Analysis.Normed.Function.Holder.C2Holder.value U‖) := by
  obtain ⟨C, hC, hdata⟩ := uniform_periodic_schauder_data hm e b hK r hr hrp hbounded hreg
    (hΩD := hΩD) hα hα1 hell hΛ hN
  refine ⟨C, hC, ?_⟩
  intro A hA hAs hAl hAu hAn hAh u hu hup hu0 F B hB hFn hFh heq U hU0 hU1 hU2
  exact hdata {
    coefficient := A
    coefficient_continuous := hA
    coefficient_symmetric := hAs
    elliptic_lower := hAl
    elliptic_upper := hAu
    coefficient_norm := hAn
    coefficient_holder := hAh
    solution := u
    solution_smooth := hu
    solution_periodic := hup
    solution_zero := hu0
    forcing := F
    forcingBound := B
    forcingBound_nonneg := hB
    forcing_norm := hFn
    forcing_holder := hFh
    equation := heq
    jets := U
    jets_value := hU0
    jets_first := hU1
    jets_second := hU2 }

end OAI.Analysis.PDE.Dirichlet
