import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Schauder
import OAI.Analysis.Calculus.Coefficients.PeriodicMooreBarrierAdmissible

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform global Schauder estimates, stated only for the actual Moore
coefficients. No inverse, solvability, or compactness is included in this premise. -/
def UniformPeriodicMooreSchauderEstimate
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} (hΩD : Ω ⊆ D) (α : ℝ) : Prop :=
  ∀ lam M : ℝ, 0 < lam → 0 < M → ∃ C : ℝ, 0 < C ∧
    ∀ ψ : CoordinateSpace n 4 → ℝ, ContDiff ℝ ∞ ψ → LatticePeriodic e lat ψ →
    (∀ x ∈ D, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
    (∀ x ∈ D, ∀ v : CoordinateSpace n 4,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v)) →
    (∀ x ∈ D, ‖detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ ≤ M) →
    (∀ x ∈ D, ∀ y ∈ D,
      ‖detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) -
        detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)‖ ≤ M * dist x y ^ α) →
    MooreDirichletSchauderSupEstimate e lat hΩD α
      (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) C

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem exists_positive_schauder_approximation
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∃ u : ℕ → CoordinateSpace n 4 → ℝ, ∃ S : ℝ, 0 < S ∧
      (∀ j, ContDiff ℝ ∞ (u j)) ∧ (∀ j, LatticePeriodic e lat (u j)) ∧
      (∀ j x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)).PosDef) ∧
      TendstoUniformlyOn (fun j x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) atTop {x | r x ≤ 0} ∧
      TendstoUniformlyOn (fun j x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
        (fun x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) atTop {x | r x ≤ 0} ∧
      (∀ j, MooreDirichletSchauderSupEstimate e lat hΩD α
        (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) S) := by
  obtain ⟨u, O, lam, M, hO, hDO, hlam, hM, hu, hup, hupos, hdiv,
    hell, hnorm, hholder, hmatnorm, hmatholder, hHlim, hOlim, hMlim⟩ :=
    OAI.Analysis.Calculus.Coefficients.exists_periodic_admissible_cofactor_approximation hn e lat hK
      hr hrp hbounded ψ hψ hψp hψpos hα hα1
  obtain ⟨S, hS, hSb⟩ := hschauder lam M hlam hM
  refine ⟨u, S, hS, hu, hup, hupos, hHlim, hMlim, ?_⟩
  intro j
  exact hSb (u j) (hu j) (hup j) (hupos j)
    (fun x hx ↦ hell j x (hDO hx)) (hnorm j) (hholder j)

omit [FiniteDimensional ℝ P] in
theorem exists_rough_moore_solution_of_convergent_cofactor_family
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α S : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (u : ℕ → CoordinateSpace n 4 → ℝ)
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (hup : ∀ j, LatticePeriodic e lat (u j))
    (hupos : ∀ j x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)).PosDef)
    (hHlim : TendstoUniformlyOn (fun j x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) atTop {x | r x ≤ 0})
    (hMlim : TendstoUniformlyOn (fun j x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
      (fun x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) atTop {x | r x ≤ 0})
    (hSest : ∀ j, MooreDirichletSchauderSupEstimate e lat hΩD α
      (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) S) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ C * ‖f‖ ∧
        v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x := by
  obtain ⟨B, hB, N, hNb⟩ := eventually_periodic_moore_C0_bound hn e lat hK
    (hr.of_le (by simp)) hrp hbounded (hψ.of_le (by norm_num)) hψp hrpos hψpos u hMlim
  refine ⟨S * (1 + B), mul_pos hS (by linarith), ?_⟩
  intro f
  apply exists_rough_moore_solution_of_schauder_and_C0 hn e lat hK hr hrp hbounded hreg
    hα hα1 hS.le hB.le (fun j ↦ u (N + j)) (fun j ↦ hu (N + j))
    (fun j ↦ hup (N + j)) (fun j ↦ hupos (N + j))
    (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) ?_ (fun j ↦ hSest (N + j)) ?_ f
  · intro x
    exact ((OAI.Analysis.Calculus.Coefficients.tendstoUniformlyOn_nat_add hHlim N).tendsto_at x.property)
  · intro j G hG
    exact hNb (N + j) (by omega) (fun x hx ↦ hupos (N + j) x hx.le) G hG

omit [FiniteDimensional ℝ P] in
/-- Solvability for a C³ potential and genuinely arbitrary periodic Hölder
forcing. The only remaining analytic hypothesis is the uniform Schauder
estimate; smooth solvability, positive coefficient approximation, C⁰ control,
compactness, and original-exponent retention are all proved. -/
theorem exists_C3_moore_dirichlet_solution_of_uniform_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ C * ‖f‖ ∧
        v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x := by
  obtain ⟨u, S, hS, hu, hup, hupos, hHlim, hMlim, hSest⟩ :=
    exists_positive_schauder_approximation hn e lat hK hr.continuous hrp hbounded
      hα.le hα1 hschauder ψ hψ hψp hψpos
  exact exists_rough_moore_solution_of_convergent_cofactor_family hn e lat hK hr hrp hbounded
    hreg hrpos hα hα1 hS ψ hψ hψp hψpos u hu hup hupos hHlim hMlim hSest

end OAI.Analysis.PDE.Dirichlet
