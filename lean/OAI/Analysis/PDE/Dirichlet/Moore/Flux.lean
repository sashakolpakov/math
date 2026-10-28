import OAI.Analysis.PDE.Dirichlet.Moore.Matrix

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual vector flux of a scalar function in orthonormal coordinates. -/
def indexedFlux (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i ↦ ∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1))

def indexedDivergence (H : EuclideanSpace ℝ I → EuclideanSpace ℝ I)
    (x : EuclideanSpace ℝ I) : ℝ :=
  ∑ i, fderiv ℝ (fun y ↦ H y i) x (EuclideanSpace.single i 1)

theorem contDiff_indexedFlux
    {A : EuclideanSpace ℝ I → Matrix I I ℝ}
    {u : EuclideanSpace ℝ I → ℝ} (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (indexedFlux A u) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)).symm
  change ContDiff ℝ 1 (L ∘ fun x i ↦
    ∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1))
  apply L.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro j _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)

theorem indexedDivergence_flux
    {A : EuclideanSpace ℝ I → Matrix I I ℝ}
    {u : EuclideanSpace ℝ I → ℝ}
    (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ I) :
    indexedDivergence (indexedFlux A u) x =
      indexedNondivergenceOperator A u x +
        ∑ j, (∑ i, fderiv ℝ (fun y ↦ A y i j) x (EuclideanSpace.single i 1)) *
          fderiv ℝ u x (EuclideanSpace.single j 1) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have ha (i j : I) : DifferentiableAt ℝ (fun y ↦ A y i j) x :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).differentiable one_ne_zero x
  have hg (j : I) : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ u y (EuclideanSpace.single j 1)) x :=
    (hd.clm_apply contDiff_const).differentiable one_ne_zero x
  have he (i : I) :
      fderiv ℝ (fun y ↦ indexedFlux A u y i) x (EuclideanSpace.single i 1) =
        ∑ j, (A x i j *
          fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          fderiv ℝ (fun y ↦ A y i j) x (EuclideanSpace.single i 1) *
            fderiv ℝ u x (EuclideanSpace.single j 1)) := by
    change fderiv ℝ (fun y ↦ ∑ j, A y i j *
      fderiv ℝ u y (EuclideanSpace.single j 1)) x _ = _
    have hs : fderiv ℝ (fun y ↦ ∑ j, A y i j *
        fderiv ℝ u y (EuclideanSpace.single j 1)) x =
        ∑ j, fderiv ℝ (fun y ↦ A y i j *
          fderiv ℝ u y (EuclideanSpace.single j 1)) x :=
      fderiv_fun_sum (u := Finset.univ)
        (A := fun j y ↦ A y i j * fderiv ℝ u y (EuclideanSpace.single j 1))
        (fun j _ ↦ (ha i j).mul (hg j))
    rw [hs]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (ha i j) (hg j)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [OAI.Analysis.PDE.Schauder.fderiv_apply_const _ x _ _ (hd.differentiable one_ne_zero x)]
    ring
  unfold indexedDivergence
  simp_rw [he, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- The cofactor conservation law removes the first-order term in the
divergence of the Moore flux. This identifies the variational operator with
the derivative of the determinant, with its actual sign and normalization. -/
theorem moore_flux_divergence {n : ℕ} {ψ u : CoordinateSpace n 4 → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 2 u) (x : CoordinateSpace n 4) :
    indexedDivergence
      (indexedFlux (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) u) x =
        mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x := by
  have hA : ContDiff ℝ 1
      (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) :=
    (contDiff_mooreRealMatrix n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hψ)
  rw [indexedDivergence_flux hA hu]
  have hz (j : Fin n × Fin 4) :
      (∑ i, fderiv ℝ (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) i j)
        x (EuclideanSpace.single i 1)) = 0 := mooreRealMatrix_divergence hψ x j
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero]
  exact mooreRealMatrix_linearization_at _ hu.contDiffAt

theorem indexedFlux_congr_germ
    {A B : EuclideanSpace ℝ I → Matrix I I ℝ} {u v : EuclideanSpace ℝ I → ℝ}
    {x : EuclideanSpace ℝ I} (hA : A =ᶠ[𝓝 x] B) (hu : u =ᶠ[𝓝 x] v) :
    indexedFlux A u =ᶠ[𝓝 x] indexedFlux B v := by
  filter_upwards [hA, hu.eventuallyEq_nhds] with y hy hv
  simp only [indexedFlux, hy, hv.fderiv_eq]

theorem indexedDivergence_congr_germ
    {H G : EuclideanSpace ℝ I → EuclideanSpace ℝ I} {x : EuclideanSpace ℝ I}
    (h : H =ᶠ[𝓝 x] G) : indexedDivergence H x = indexedDivergence G x := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y ↦ H y i) =ᶠ[𝓝 x] (fun y ↦ G y i) := h.fun_comp (fun z ↦ z i)
  rw [hi.fderiv_eq]

theorem moore_flux_divergence_at {n : ℕ} {ψ u : CoordinateSpace n 4 → ℝ}
    {x : CoordinateSpace n 4} (hψ : ContDiffAt ℝ 3 ψ x) (hu : ContDiffAt ℝ 2 u x) :
    indexedDivergence
      (indexedFlux (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) u) x =
        mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x := by
  obtain ⟨Ψ, hΨ, heΨ⟩ := exists_contDiff_extension_near_point hψ
  obtain ⟨v, hv, hev⟩ := exists_contDiff_extension_near_point hu
  have hH : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots Ψ =ᶠ[𝓝 x] quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ := by
    filter_upwards [heΨ.eventuallyEq_nhds] with y hy
    exact quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hy
  have hflux := indexedFlux_congr_germ
    (hH.fun_comp (fun a ↦ mooreRealMatrix a)) hev
  simp only [Function.comp_def] at hflux
  rw [← indexedDivergence_congr_germ hflux, moore_flux_divergence hΨ hv]
  unfold mooreLinearization
  rw [hH.self_of_nhds, quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hev]

end OAI.Analysis.PDE.Dirichlet
