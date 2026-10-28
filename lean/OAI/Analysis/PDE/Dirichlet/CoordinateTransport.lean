import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Linear
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation
import OAI.Analysis.PDE.Dirichlet.Hessian

open Set
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

theorem second_fderiv_comp_between {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : F → ℝ) (hu : ContDiff ℝ 2 u) (L : E →L[ℝ] F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (u ∘ L)) x v w =
      fderiv ℝ (fderiv ℝ u) (L x) (L v) (L w) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDcomp : ContDiff ℝ 1 (fderiv ℝ (u ∘ L)) :=
    (hu.comp L.contDiff).fderiv_right (by norm_num)
  have he : (fun y ↦ fderiv ℝ (u ∘ L) y w) = fun y ↦ fderiv ℝ u (L y) (L w) := by
    funext y
    rw [fderiv_comp y (hu.differentiable (by norm_num) _) L.differentiableAt, L.fderiv]
    rfl
  rw [← OAI.Analysis.PDE.Schauder.fderiv_apply_const _ x w v (hDcomp.differentiable one_ne_zero x), he]
  have hfun : (fun y ↦ fderiv ℝ u (L y) (L w)) = (fun y ↦ fderiv ℝ u y (L w)) ∘ L := rfl
  rw [hfun, fderiv_comp x ((hD.clm_apply contDiff_const).differentiable one_ne_zero _)
    L.differentiableAt, L.fderiv, ContinuousLinearMap.comp_apply,
    OAI.Analysis.PDE.Schauder.fderiv_apply_const _ (L x) (L w) (L v) (hD.differentiable one_ne_zero _)]

def coordinateReindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ J :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem coordinateReindex_symm_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (x : EuclideanSpace ℝ I) :
    coordinateReindex e.symm (coordinateReindex e x) = x := by
  have he : coordinateReindex e.symm = (coordinateReindex e).symm := by
    exact (LinearIsometryEquiv.piLpCongrLeft_symm e).symm
  rw [he, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem coordinateReindex_single {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (i : I) (c : ℝ) :
    coordinateReindex e (EuclideanSpace.single i c) = EuclideanSpace.single (e i) c :=
  EuclideanSpace.piLpCongrLeft_single e i c

def indexedNondivergenceOperator {I : Type*} [Fintype I] [DecidableEq I]
    (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (x : EuclideanSpace ℝ I) : ℝ :=
  ∑ i : I, ∑ j : I, A x i j * fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Reindexing the actual Hessian equation preserves the operator exactly,
not just its symbol or an abstract coefficient representation. -/
theorem indexedNondivergenceOperator_reindex {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (e : I ≃ J)
    (A : EuclideanSpace ℝ J → Matrix J J ℝ)
    (u : EuclideanSpace ℝ J → ℝ) (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ I) :
    indexedNondivergenceOperator
      (fun y i j ↦ A (coordinateReindex e y) (e i) (e j))
      (u ∘ coordinateReindex e) x =
      indexedNondivergenceOperator A u (coordinateReindex e x) := by
  let L := (coordinateReindex e).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (i j : I) : fderiv ℝ (fderiv ℝ (u ∘ coordinateReindex e)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fderiv ℝ u) (coordinateReindex e x)
        (EuclideanSpace.single (e i) 1) (EuclideanSpace.single (e j) 1) := by
    simpa only [L, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, coordinateReindex_single] using
      second_fderiv_comp_between u hu L x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  unfold indexedNondivergenceOperator
  simp_rw [hD]
  calc
    _ = ∑ i : I, ∑ j : J, A (coordinateReindex e x) (e i) j *
        fderiv ℝ (fderiv ℝ u) (coordinateReindex e x)
          (EuclideanSpace.single (e i) 1) (EuclideanSpace.single j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j : J ↦ A (coordinateReindex e x) (e i) j *
        fderiv ℝ (fderiv ℝ u) (coordinateReindex e x)
          (EuclideanSpace.single (e i) 1) (EuclideanSpace.single j 1))
    _ = _ := e.sum_comp (fun i : J ↦ ∑ j : J, A (coordinateReindex e x) i j *
      fderiv ℝ (fderiv ℝ u) (coordinateReindex e x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

def flattenFourSlots (n : ℕ) :
    CoordinateSpace n 4 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n * 4)) :=
  coordinateReindex finProdFinEquiv

end OAI.Analysis.PDE.Dirichlet
