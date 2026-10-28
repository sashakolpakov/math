import OAI.Analysis.PDE.Elliptic.Boundary.VectorField
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Fields

noncomputable section
open Filter Set
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

theorem fieldDerivative_congr_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {T R : E → E} {x : E}
    (hu : u =ᶠ[𝓝 x] v) (hT : T =ᶠ[𝓝 x] R) :
    fieldDerivative u T =ᶠ[𝓝 x] fieldDerivative v R := by
  filter_upwards [hu.fderiv (𝕜 := ℝ), hT] with y hy hz
  simp only [fieldDerivative, hy, hz]

/-- The exact equation only requires C³ at the interior point. -/
theorem log_equation_fieldDerivative_eq_at {n : ℕ}
    {u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} (hu : ContDiffAt ℝ 3 u x) (hT : ContDiffAt ℝ 2 T x)
    (hf : DifferentiableAt ℝ f x)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 x] f) :
    ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (fieldDerivative u T) x = fderiv ℝ f x (T x) / f x +
        fieldCommutator (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) u T x := by
  obtain ⟨v, hv, hvu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  obtain ⟨R, hR, hRT⟩ := exists_contDiff_extension_near_compact
    (K := {x}) isCompact_singleton (fun y hy => by simpa using (mem_singleton_iff.mp hy) ▸ hT)
  have hRT := hRT x (mem_singleton x)
  have hHv := OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hvu
  have hveq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v y)) =ᶠ[𝓝 x] f := by
    filter_upwards [hvu.eventuallyEq_nhds, heq] with y hy hz
    rwa [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hy]
  have h := log_equation_fieldDerivative_eq hv hR hf hveq
  rw [ellipticTrace_congr_germ _ (fieldDerivative_congr_germ hvu hRT)] at h
  have hD := hvu.fderiv_eq (𝕜 := ℝ)
  have hDD := (hvu.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hDT := hRT.fderiv_eq (𝕜 := ℝ)
  have hDDT := (hRT.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  simpa only [ellipticTrace, fieldCommutator, hHv, hD, hDD, hDT, hDDT, hRT.eq_of_nhds] using h

/-- The tangent derivative in flat coordinates is the pullback of an actual
variable-field derivative in the physical coordinates. -/
theorem chart_field_comp_germ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {G P : E → E} {u : E → ℝ} {y : E} (e : E)
    (hG : Differentiable ℝ G) (hu : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ u (G z))
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 y] id) :
    (fun z => fieldDerivative u (chartTangentField G P e) (G z)) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ (fun q => u (G q)) z e) := by
  filter_upwards [hu, hinv] with z hz hi
  have hd : fderiv ℝ (fun q => u (G q)) z =
      (fderiv ℝ u (G z)).comp (fderiv ℝ G z) :=
    (hz.hasFDerivAt.comp z (hG z).hasFDerivAt).fderiv
  simp only [hd, fieldDerivative, chartTangentField, hi, id_eq, ContinuousLinearMap.comp_apply]

/-- The differentiated nonlinear equation in the genuine curved-boundary
chart. Its second-order operator has the transformed coefficient, and the
only additional first-order term is the explicitly computed chart drift. -/
theorem log_equation_chart_tangent {n : ℕ}
    {u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {G P : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P) (e y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hu : ContDiffAt ℝ 3 u (G y)) (hf : DifferentiableAt ℝ f (G y))
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 y] id)
    (heq : (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) =ᶠ[𝓝 (G y)] f) :
    let A := fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)
    let w := fun z => fderiv ℝ (fun q => u (G q)) z e
    ellipticTrace (fun z => pullbackEllipticOperator (fderiv ℝ P (G z)) (A (G z))) w y =
      fderiv ℝ f (G y) (fderiv ℝ G y e) / f (G y) +
      fieldCommutator A u (chartTangentField G P e) (G y) +
      fderiv ℝ w y (inverseChartDrift A G P y) := by
  dsimp only
  let T := chartTangentField G P e
  let A := fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)
  have hT : ContDiff ℝ 2 T := contDiff_chartTangentField hG hP e
  have hW : ContDiffAt ℝ 2 (fieldDerivative u T) (G y) :=
    (hu.fderiv_right (by norm_num)).clm_apply hT.contDiffAt
  have hUn : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ u (G z) := by
    have hn : ∀ᶠ z in 𝓝 (G y), ContDiffAt ℝ 3 u z := hu.eventually (by norm_num)
    filter_upwards [hG.continuous.continuousAt.tendsto.eventually hn] with z hz
    exact hz.differentiableAt (by norm_num)
  have hw := chart_field_comp_germ e (hG.differentiable (by norm_num)) hUn hinv
  have hchange := ellipticTrace_inverse_chart_with_drift A
    (hP.differentiable (by norm_num) (G y)) (hG.of_le (by norm_num)).contDiffAt hW hinv
  rw [ellipticTrace_congr_germ _ hw, hw.fderiv_eq (𝕜 := ℝ)] at hchange
  rw [log_equation_fieldDerivative_eq_at hu hT.contDiffAt hf heq] at hchange
  have hTy : T (G y) = fderiv ℝ G y e := by
    simp only [T, chartTangentField, hinv.eq_of_nhds, id_eq]
  simpa only [hTy, T, A] using hchange

end OAI.Analysis.PDE.Elliptic
