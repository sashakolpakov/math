import OAI.Analysis.PDE.Dirichlet.Path.LimitData
import OAI.Analysis.PDE.Nonlinear.BanachBootstrap
import OAI.Analysis.PDE.Nonlinear.Fourth

open Set Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
  {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
  {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}

/-- The actual compactness limit is C³ in the interior, by the nonlinear
Moore bootstrap; this regularity is not built into the limit record. -/
theorem BanachPathLimit.contDiffOn_three
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t)
    (hn : 1 ≤ n) (hβ : 0 < β) (hβ1 : β < 1) (hr : Continuous r)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁) :
    ContDiffOn ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x < 0} := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  change ContDiffOn ℝ 3 (OAI.Analysis.PDE.Nonlinear.banachJetFunction L.value) {x | r x < 0}
  apply OAI.Analysis.PDE.Nonlinear.moore_C3_of_banach_jet (by omega) hβ hβ1 hΩ hΩK L.value
    (densityPath F₀ F₁ t) (contDiff_densityPath hF₀ hF₁ t).contDiffOn
  · intro x hx
    change OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) x) = densityPath F₀ F₁ t x
    rw [← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots L.value hx]
    exact (L.admissible ⟨x, hΩK hx⟩).1
  · intro x hx
    change (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) x)).PosDef
    rw [← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots L.value hx]
    exact (L.admissible ⟨x, hΩK hx⟩).2

/-- The same actual compactness limit has the fourth interior derivative
needed by the nonlinear a priori estimates. Boundary regularity is a
separate issue and is not asserted here. -/
theorem BanachPathLimit.contDiffOn_four
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t)
    (hn : 1 ≤ n) (hβ : 0 < β) (hβ1 : β < 1) (hr : Continuous r)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x < 0} := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  have hF : ContDiff ℝ 3 (densityPath F₀ F₁ t) :=
    (contDiff_const.mul hF₀).add (contDiff_const.mul hF₁)
  apply OAI.Analysis.PDE.Nonlinear.moore_C4On_of_C3On (by omega)
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) (densityPath F₀ F₁ t) hΩ
    (L.contDiffOn_three hn hβ hβ1 hr (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num)))
    hF.contDiffOn
  · intro x hx
    rw [← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots L.value hx]
    exact (L.admissible ⟨x, hΩK hx⟩).1
  · intro x hx
    rw [← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots L.value hx]
    exact (L.admissible ⟨x, hΩK hx⟩).2

end OAI.Analysis.PDE.Dirichlet
