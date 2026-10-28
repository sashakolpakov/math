import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Initial
import OAI.Analysis.PDE.Dirichlet.Boundary.UniformDefining
import OAI.Analysis.PDE.Schauder.Calculus.Interior.PathData

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4

/-- All uniform lower-order path data follow from the original defining
function, background and positive prescribed density. -/
theorem nonempty_initialPathData
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ ∞ B₀) (hF : ContDiff ℝ ∞ F)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hFp : LatticePeriodic e lat F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hpos : ∀ x, r x ≤ 0 → 0 < F x) :
    Nonempty (OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ (initialDensity B₀ r) F hΩK) := by
  have hF₀ := contDiff_initialDensity_infty hB₀ hr
  have hp₀ := initialDensity_periodic e lat hBp hrp
  have hpos₀ : ∀ x, r x ≤ 0 → 0 < initialDensity B₀ r x := fun x hx =>
    initialDensity_pos (hB₀.of_le (by simp)) (hr.of_le (by simp)) (hbase x hx) (hrpos x hx)
  obtain ⟨r₀,hr₀,hshift⟩ := uniform_defining_hessian_shift (by omega) e lat hK
    (hr.of_le (by simp)) hrp hbounded hne hrpos
  exact OAI.Analysis.PDE.Schauder.nonempty_interiorThirdPathData e lat hK
    (hr.of_le (by simp)) (hB₀.of_le (by simp)) (hF₀.of_le (by simp)) (hF.of_le (by simp))
    hrp hBp hp₀ hFp hbounded hne hreg hr₀ hpos₀ hpos hbase hdet hshift

end OAI.Analysis.PDE.Dirichlet
