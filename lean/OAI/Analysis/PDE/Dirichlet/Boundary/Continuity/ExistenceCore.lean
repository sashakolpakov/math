import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Compact
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Data
import OAI.Analysis.PDE.Schauder.Dirichlet.UniformFourthRegularity

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4

/-- Initial solvability and actual fourth-order compactness reduce global
solvability to the local continuation step. -/
theorem moore_densityPath_solvable_of_open
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
    (hpos : ∀ x, r x ≤ 0 → 0 < F x)
    (hopen : ∀ s : SmoothPathSolution e lat r B₀ (initialDensity B₀ r) F,
      ∀ᶠ t in 𝓝 s.t, t ∈ Icc (0 : ℝ) 1 →
        SmoothPathSolvable e lat r B₀ (initialDensity B₀ r) F t) :
    ∀ t ∈ Icc (0 : ℝ) 1, SmoothPathSolvable e lat r B₀ (initialDensity B₀ r) F t := by
  let : Nonempty {x | r x ≤ 0} := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  let hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0} := fun x hx => (show r x < 0 from hx).le
  have hF₀ := contDiff_initialDensity_infty hB₀ hr
  have hp₀ := initialDensity_periodic e lat hBp hrp
  have hpos₀ : ∀ x, r x ≤ 0 → 0 < initialDensity B₀ r x := fun x hx =>
    initialDensity_pos (hB₀.of_le (by simp)) (hr.of_le (by simp)) (hbase x hx) (hrpos x hx)
  obtain ⟨d⟩ := nonempty_initialPathData (hΩK := hΩD) e lat hK hr hB₀ hF
    hrp hBp hFp hbounded hne hreg hrpos hbase hdet hpos
  have hfourth := d.uniform_fourth_holder e lat hK hr (hB₀.of_le (by simp))
    (hF₀.of_le (by simp)) (hF.of_le (by simp)) hrp hBp hp₀ hFp hbounded hreg hrpos hpos₀ hpos
  have hlimits : HasC4PathLimits e lat d := hasC4PathLimits_of_uniform_fourth e lat hK d hr
    (hB₀.of_le (by simp)) (hF₀.of_le (by simp)) (hF.of_le (by simp))
    hrp hBp hp₀ hFp hbounded hne hreg hpos₀ hpos hfourth
  apply OAI.Analysis.PDE.Dirichlet.SmoothPathSolvable.all_parameters e lat
  · exact ⟨OAI.Analysis.PDE.Dirichlet.SmoothPathSolution.initial e lat r B₀ F
      (hr.of_le (by simp)) (hB₀.of_le (by simp)) hrp hbase hrpos,rfl⟩
  · exact OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.sequentially_closed_of_C4_limits e lat hK d hr
      (hB₀.of_le (by simp)) (hF₀.of_le (by simp)) (hF.of_le (by simp))
      hrp hBp hbounded hreg hpos₀ hpos hlimits
  · exact hopen

end OAI.Analysis.PDE.Dirichlet
