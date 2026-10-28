import OAI.Analysis.PDE.Dirichlet.Linear.Divergence

open Set Filter InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

section LinearCoordinates
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem gradient_comp_linearEquiv (L : E ≃L[ℝ] F) {u : F → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (L x)) :
    gradient (u ∘ L) x = L.toContinuousLinearMap.adjoint (gradient u (L x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
  rw [fderiv_comp x hu L.differentiableAt, L.fderiv]
  rfl

theorem inverse_adjoint_cancel (L : E ≃L[ℝ] F) (v : F) :
    L.symm.toContinuousLinearMap.adjoint (L.toContinuousLinearMap.adjoint v) = v := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- Contravariant coefficient pullback. The adjoint on the right accounts
for the gradient, while the inverse on the left accounts for the flux. -/
def linearPullbackCoefficient (L : E ≃L[ℝ] F) (A : F → F →L[ℝ] F) (x : E) : E →L[ℝ] E :=
  L.symm.toContinuousLinearMap.comp
    ((A (L x)).comp L.symm.toContinuousLinearMap.adjoint)

theorem linearPullbackCoefficient_flux (L : E ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) {u : F → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (L x)) :
    linearPullbackCoefficient L A x (gradient (u ∘ L) x) = L.symm (A (L x) (gradient u (L x))) := by
  simp only [linearPullbackCoefficient, ContinuousLinearMap.comp_apply,
    gradient_comp_linearEquiv L hu, inverse_adjoint_cancel, ContinuousLinearEquiv.coe_coe]

theorem linearPullbackCoefficient_quadratic (L : E ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) (x v : E) :
    inner ℝ (linearPullbackCoefficient L A x v) v =
      inner ℝ (A (L x) (L.symm.toContinuousLinearMap.adjoint v))
        (L.symm.toContinuousLinearMap.adjoint v) := by
  change inner ℝ (L.symm.toContinuousLinearMap
    (A (L x) (L.symm.toContinuousLinearMap.adjoint v))) v = _
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

end LinearCoordinates

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Exact transformation of the differential operator under an arbitrary
constant linear change of coordinates, including nonorthogonal lattices. -/
theorem divergence_linearPullbackCoefficient
    (L : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ J)
    {A : EuclideanSpace ℝ J → EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J}
    {u : EuclideanSpace ℝ J → ℝ} (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ I) :
    indexedDivergence (fun y ↦ linearPullbackCoefficient L A y (gradient (u ∘ L) y)) x =
      indexedDivergence (fun y ↦ A y (gradient u y)) (L x) := by
  have hg : ContDiff ℝ 1 (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ J)).symm.contDiff.comp (hu.fderiv_right (by norm_num))
  have he : (fun y ↦ linearPullbackCoefficient L A y (gradient (u ∘ L) y)) =
      (fun y ↦ L.symm (A (L y) (gradient u (L y)))) := by
    funext y
    exact linearPullbackCoefficient_flux L A (hu.differentiable (by norm_num) _)
  rw [he]
  exact indexedDivergence_linear_pullback L ((hA.clm_apply hg).differentiable one_ne_zero _)

theorem indexedFlux_eq_matrix_gradient (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (x : EuclideanSpace ℝ I) :
    indexedFlux A u x = Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (A x) (gradient u x) := by
  apply PiLp.ext
  intro i
  change (∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1)) =
    ∑ j, A x i j * (gradient u x) j
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [EuclideanSpace.inner_single_right, mul_one, one_mul,
    starRingEnd_apply, star_trivial] using
    (inner_gradient_left (f := u) (x := x) (y := EuclideanSpace.single j 1)).symm

/-- The concrete Moore equation survives the full nonorthogonal change of
coordinates used to make an arbitrary lattice into a coordinate lattice. -/
theorem moore_flux_divergence_linear_pullback {n : ℕ}
    (L : EuclideanSpace ℝ I ≃L[ℝ] CoordinateSpace n 4)
    {ψ u : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ I) :
    indexedDivergence (fun y ↦ linearPullbackCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
        (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z))) y
      (gradient (u ∘ L) y)) x =
        mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u (L x) := by
  let A := fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)
  have hA : ContDiff ℝ 1 A :=
    (contDiff_mooreRealMatrix n 1).comp
      (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hψ)
  have he : (fun y ↦ linearPullbackCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (A z)) y
        (gradient (u ∘ L) y)) = (fun y ↦ L.symm (indexedFlux A u (L y))) := by
    funext y
    rw [linearPullbackCoefficient_flux L _ (hu.differentiable (by norm_num) _),
      ← indexedFlux_eq_matrix_gradient A u]
  change indexedDivergence (fun y ↦ linearPullbackCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (A z)) y
        (gradient (u ∘ L) y)) x = _
  rw [he, indexedDivergence_linear_pullback L
    ((contDiff_indexedFlux hA hu).differentiable one_ne_zero _)]
  exact moore_flux_divergence hψ hu _

end OAI.Analysis.PDE.Dirichlet
