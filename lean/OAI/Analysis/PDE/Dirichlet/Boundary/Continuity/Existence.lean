import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Compact
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Open
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Initial
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Endpoint
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Data
import OAI.Analysis.PDE.Dirichlet.Boundary.UniformDefining
import OAI.Analysis.PDE.Schauder.Dirichlet.UniformFourthRegularity
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.ExistenceCore

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4

/-- The continuity path is solvable at every parameter. All compactness,
ellipticity, inverse and higher-regularity estimates are derived from the
fixed geometric and density data; none is assumed here. -/
theorem moore_densityPath_solvable
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ ∞ B₀) (hF : ContDiff ℝ ∞ F)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hFp : LatticePeriodic e lat F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hpos : ∀ x, r x ≤ 0 → 0 < F x) :
    ∀ t ∈ Icc (0 : ℝ) 1, SmoothPathSolvable e lat r B₀ (initialDensity B₀ r) F t := by
  let : Nonempty {x | r x ≤ 0} := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hF₀ : ContDiff ℝ ∞ (initialDensity B₀ r) := contDiff_initialDensity_infty hB₀ hr
  have hp₀ := initialDensity_periodic e lat hBp hrp
  have hpos₀ : ∀ x, r x ≤ 0 → 0 < initialDensity B₀ r x := fun x hx =>
    initialDensity_pos (hB₀.of_le (by simp)) (hr.of_le (by simp)) (hbase x hx) (hrpos x hx)
  apply moore_densityPath_solvable_of_open e lat hK hr hB₀ hF hrp hBp hFp
    hbounded hne hreg hrpos hbase hdet hpos
  intro s
  exact s.solvable_near (by omega) e lat hK hr hB₀ hF₀ hF hrp hBp hp₀ hFp
    hbounded hreg hrpos hpos₀ hpos

/-- Actual periodic C⁴ Dirichlet solvability for the positive quaternionic
Monge--Ampère equation, with the original smooth fixed-data hypotheses. -/
theorem exists_periodic_moore_dirichlet_C4
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ ∞ B₀) (hF : ContDiff ℝ ∞ F)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hFp : LatticePeriodic e lat F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hpos : ∀ x, r x ≤ 0 → 0 < F x) :
    ∃ ψ : E → ℝ, ContDiff ℝ 4 ψ ∧ LatticePeriodic e lat ψ ∧
      (∀ x, r x = 0 → ψ x = B₀ x) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) := by
  have hs := moore_densityPath_solvable e lat hK hr hB₀ hF hrp hBp hFp
    hbounded hne hreg hrpos hbase hdet hpos 1 (by constructor <;> norm_num)
  have hF₀ := contDiff_initialDensity_infty hB₀ hr
  have hpos₀ : ∀ x, r x ≤ 0 → 0 < initialDensity B₀ r x := fun x hx =>
    initialDensity_pos (hB₀.of_le (by simp)) (hr.of_le (by simp)) (hbase x hx) (hrpos x hx)
  exact hs.classical_endpoint (hr.of_le (by simp)) (hB₀.of_le (by simp))
    hF₀.continuous hF.continuous hBp hreg hpos₀ hpos

end OAI.Analysis.PDE.Dirichlet
