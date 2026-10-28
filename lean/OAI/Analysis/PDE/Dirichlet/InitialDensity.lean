import OAI.Analysis.PDE.Dirichlet.Path.C2
import OAI.Analysis.PDE.Dirichlet.HessianMapNorm
import OAI.LinearAlgebra.Moore.Smooth

open Set Module
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem contDiff_quaternionHessian_two {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ : CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 4 ψ) :
    ContDiff ℝ 2 (quaternionHessian e ψ) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
  have hH : ContDiff ℝ 2 (realHessian ψ) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (hD.clm_apply contDiff_const).clm_apply contDiff_const
  exact (hessianMatrixCLM e).contDiff.comp hH

/-- The initial density is the actual determinant of the defining-function
solution, not separately supplied data. -/
def initialDensity {n : ℕ} (B₀ r : CoordinateSpace n 4 → ℝ) (x : CoordinateSpace n 4) : ℝ :=
  OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + r y) x)

theorem contDiff_initialDensity {n : ℕ} {B₀ r : CoordinateSpace n 4 → ℝ}
    (hB : ContDiff ℝ 4 B₀) (hr : ContDiff ℝ 4 r) :
    ContDiff ℝ 2 (initialDensity B₀ r) :=
  (OAI.LinearAlgebra.Moore.contDiff_mooreDet n 2).comp (contDiff_quaternionHessian_two OAI.Analysis.Calculus.Quaternion.fourSlots (hB.add hr))

theorem initialDensity_pos {n : ℕ} {B₀ r : CoordinateSpace n 4 → ℝ}
    (hB : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r) {x : CoordinateSpace n 4}
    (hbase : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef) :
    0 < initialDensity B₀ r x := by
  apply OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef
  have hadd := quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB hr (1 : ℝ) x
  simp only [one_smul] at hadd
  rw [hadd, OAI.LinearAlgebra.Moore.complexify_add]
  exact Matrix.PosDef.posSemidef_add hbase hconvex

theorem initialDensity_periodic {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {B₀ r : CoordinateSpace n 4 → ℝ}
    (hB : LatticePeriodic e lat B₀) (hr : LatticePeriodic e lat r) :
    LatticePeriodic e lat (initialDensity B₀ r) :=
  ((hB.add hr).quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp (OAI.LinearAlgebra.Moore.mooreDet n)

theorem initialDensity_path_zero {n : ℕ} (B₀ r F : CoordinateSpace n 4 → ℝ) :
    densityPath (initialDensity B₀ r) F 0 = initialDensity B₀ r := by
  funext x
  simp [densityPath]

theorem initialDensity_path_one {n : ℕ} (B₀ r F : CoordinateSpace n 4 → ℝ) :
    densityPath (initialDensity B₀ r) F 1 = F := by
  funext x
  simp [densityPath]

end OAI.Analysis.PDE.Dirichlet
