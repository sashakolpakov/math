import OAI.Analysis.Calculus.Coefficients.Positive
import OAI.Analysis.PDE.Dirichlet.Moore.Bilinear

open Set Filter Module Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Calculus.Coefficients

/-- The matrix coefficient used by the weak solver is exactly the actual
real linearization operator, with no normalization factor. -/
theorem toEuclideanCLM_mooreRealMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (mooreRealMatrix A) =
      detRealOperator A := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  simpa only [Matrix.inner_toEuclideanCLM,star_trivial] using mooreRealMatrix_bilinear A w v

theorem contDiff_toEuclideanCLM_mooreRealMatrix (n : ℕ) (q : ℕ∞ω) :
    ContDiff ℝ q (fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
      Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (mooreRealMatrix A)) := by
  simpa only [toEuclideanCLM_mooreRealMatrix] using contDiff_detRealOperator n q

/-- Genuine smoothness of the concrete coefficient field of a smooth
potential, in the operator norm used by the variational solver. -/
theorem contDiff_smooth_mooreCoefficient {n : ℕ}
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun x ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
      (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x))) :=
  (contDiff_toEuclideanCLM_mooreRealMatrix n ∞).comp (OAI.Analysis.Calculus.Coefficients.contDiff_quaternionHessian_smooth hψ)

variable {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem LatticePeriodic.mooreCoefficient
    {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : LatticePeriodic e b ψ) :
    LatticePeriodic e b (fun x ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
      (mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x))) :=
  (hψ.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp
    (fun A ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (mooreRealMatrix A))

/-- A single smooth admissible periodic potential has a uniformly elliptic
concrete matrix coefficient on an open neighborhood of the entire closed
periodic domain. Only the transverse fundamental-cell geometry is compact. -/
theorem smooth_mooreCoefficient_elliptic_neighborhood
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : CoordinateSpace n 4 → ℝ}
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψp : LatticePeriodic e b ψ)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∃ O : Set (CoordinateSpace n 4), ∃ lam : ℝ,
      IsOpen O ∧ {x | r x ≤ 0} ⊆ O ∧ 0 < lam ∧
      ∀ x ∈ O, ∀ v : CoordinateSpace n 4,
        lam*‖v‖^2 ≤ inner ℝ v
          (Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
            (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) v) := by
  let A := fun x ↦ detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
  let S := latticeSublevelCell e b K r
  have hS : IsCompact S := isCompact_latticeSublevelCell e b hK hr
  have hAc : Continuous A :=
    (contDiff_detRealOperator n ∞).continuous.comp (OAI.Analysis.Calculus.Coefficients.contDiff_quaternionHessian_smooth hψ).continuous
  have hAp : LatticePeriodic e b A := (hψp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp detRealOperator
  obtain ⟨lam,hlam,hell⟩ := OAI.Analysis.Calculus.Coefficients.compact_positive_cofactor_lower hn hS ψ (hψ.of_le (by simp))
    (fun x hx ↦ hpos x hx.2)
  have hc : TendstoUniformlyOn (fun _ : ℕ ↦ A) A atTop (cthickening 1 S) := by
    refine (Metric.tendstoUniformlyOn_iff (α := CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)).mpr ?_
    intro ε hε
    exact Eventually.of_forall (fun j x hx ↦ by simpa using hε)
  obtain ⟨O,hO,hDO,N,hN⟩ := OAI.Analysis.Calculus.Coefficients.periodic_elliptic_neighborhood e b A hAc (fun _ : ℕ ↦ A)
    (fun _ ↦ hAp) hS (fun x hx ↦ latticeRepresentative_mem_sublevelCell e b hrp hbounded hx)
    hc hlam hell
  refine ⟨O,lam/2,hO,hDO,by positivity,?_⟩
  intro x hx v
  simpa only [toEuclideanCLM_mooreRealMatrix] using hN N le_rfl x hx v

end OAI.Analysis.PDE.Dirichlet
