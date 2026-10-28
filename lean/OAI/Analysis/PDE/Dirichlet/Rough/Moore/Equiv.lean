import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Inverse

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
/-- An actual continuous linear inverse for the periodic derivative. Its
existence is derived from the rough-data solver and maximum principle, not
assumed as an anonymous inverse in the continuity method. -/
theorem exists_periodicMooreDirichlet_derivative_equiv_of_uniform_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hH : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :
    ∃ L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat ≃L[ℝ]
        OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      fderiv ℝ (periodicMooreDirichletOperator
        (isOpen_lt hr.continuous continuous_const) hclosure
        (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u =
          L.toContinuousLinearMap := by
  let : Fact (IsOpen {x | r x < 0}) := ⟨isOpen_lt hr.continuous continuous_const⟩
  let X := OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat
  let Y := OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat
  let T : X →L[ℝ] Y := fderiv ℝ (periodicMooreDirichletOperator
    (isOpen_lt hr.continuous continuous_const) hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u
  have hbij : Function.Bijective T :=
    fderiv_periodicMooreDirichletOperator_bijective_of_uniform_schauder
      hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1 hschauder ψ hψ hψp hψpos v hv u hH
  let L : X ≃L[ℝ] Y := ContinuousLinearEquiv.ofBijective
    (E := X) (F := Y) (σ := RingHom.id ℝ) (σ' := RingHom.id ℝ) T
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  refine ⟨L, ?_⟩
  apply ContinuousLinearMap.ext
  intro w
  rfl

end OAI.Analysis.PDE.Dirichlet
