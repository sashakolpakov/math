import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJet
import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit

noncomputable section
open Set Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

local instance smoothDataDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance smoothDataDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance smoothDataSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance smoothDataSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance smoothDataC2Group : NormedAddCommGroup H := inferInstance
local instance smoothDataC2Space : NormedSpace ℝ H := inferInstance
local instance smoothDataC2Module : Module ℝ H := inferInstance
local instance smoothDataC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance smoothDataC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance smoothDataC2AddZero : AddZeroClass H := inferInstance

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
/-- A classical C³ potential and its boundary background supply actual
closed-domain jets with a genuine zero-boundary increment. -/
theorem exists_smooth_moore_jet_data
    {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 < α) (hα1 : α < 1)
    (B₀ ψ : E → ℝ) (hB₀ : ContDiff ℝ 3 B₀) (hψ : ContDiff ℝ 3 ψ)
    (hB₀p : LatticePeriodic e b B₀) (hψp : LatticePeriodic e b ψ)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x) :
    ∃ (B : H) (u : X) (_ : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B))),
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
        fderiv ℝ (fderiv ℝ ψ) x) := by
  obtain ⟨B,_,_,_,hBv,_,hB₂,hBp⟩ := exists_periodic_C2Holder_jet e b hK hr.continuous
    hrp hbounded (hΩD := hΩK) B₀ hB₀ hB₀p hα.le hα1.le
  obtain ⟨g,_,_,_,hgv,_,hg₂,hgp⟩ := exists_periodic_C2Holder_jet e b hK hr.continuous
    hrp hbounded (hΩD := hΩK) ψ hψ hψp hα.le hα1.le
  have humem : g-B ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e b := by
    constructor
    · intro x hx
      change OAI.Analysis.Normed.Function.Holder.C2Holder.value g x - OAI.Analysis.Normed.Function.Holder.C2Holder.value B x = 0
      rw [hgv,hBv,hψbd x (le_antisymm x.property (not_lt.mp hx)),sub_self]
    · change LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g-OAI.Analysis.Normed.Function.Holder.C2Holder.value B))
      have hext : OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g-OAI.Analysis.Normed.Function.Holder.C2Holder.value B) =
          fun x ↦ OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g) x -
            OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B) x := by
        funext x
        by_cases hx : r x ≤ 0 <;> simp [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension,zeroExtend,hx]
      rw [hext]
      intro x l
      dsimp only
      rw [hgp x l,hBp x l]
  let u : X := ⟨g-B,humem⟩
  have hfull : B+u.val = g := by
    change B+(g-B)=g
    abel
  have hjet (x : {x | r x ≤ 0}) : OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
      fderiv ℝ (fderiv ℝ ψ) x := by
    rw [hfull]
    exact hg₂ x
  exact ⟨B,u,hBp,hB₂,hjet⟩

omit [FiniteDimensional ℝ P] in
/-- The actual derivative for those jets is invertible, by the proved
linear Dirichlet theorem. -/
theorem smooth_moore_data_invertible
    (hn : 1 ≤ n) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    (hα : 0 < α) (hα1 : α < 1)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e b ψ)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (B : H) (u : X) (hBp : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (hjet : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
      fderiv ℝ (fderiv ℝ ψ) x) :
    (fderiv ℝ (periodicMooreDirichletOperator (isOpen_lt hr.continuous continuous_const)
      hclosure (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots B hBp) u).IsInvertible := by
  have hH (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val) ψ x (hjet x)
  obtain ⟨L,hL⟩ := exists_periodicMooreDirichlet_derivative_equiv_unconditional
    hn e b hK hr hrp hbounded hreg hrpos hclosure hα hα1 ψ hψ hψp hpos B hBp u hH
  rw [hL]
  exact ⟨L,rfl⟩

end OAI.Analysis.PDE.Dirichlet
