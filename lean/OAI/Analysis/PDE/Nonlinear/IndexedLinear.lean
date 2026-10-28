import OAI.Analysis.PDE.Nonlinear.LocalTransport

/-! The actual local C³ linear theorem in arbitrary finite Euclidean coordinates. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

local instance indexedLinearFirstGroup (I : Type*) [Fintype I] :
    NormedAddCommGroup (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance indexedLinearFirstSpace (I : Type*) [Fintype I] :
    NormedSpace ℝ (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance indexedLinearSecondGroup (I : Type*) [Fintype I] :
    NormedAddCommGroup (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance indexedLinearSecondSpace (I : Type*) [Fintype I] :
    NormedSpace ℝ (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance indexedLinearMatrixDGroup (I : Type*) [Fintype I] :
    NormedAddCommGroup (EuclideanSpace ℝ I →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ I →L[ℝ] (I → I → ℝ)))
local instance indexedLinearMatrixDSpace (I : Type*) [Fintype I] :
    NormedSpace ℝ (EuclideanSpace ℝ I →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ I →L[ℝ] (I → I → ℝ)))

theorem indexed_linear_C3At {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (e : I ≃ Fin m) (hm : 3 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u f : EuclideanSpace ℝ I → ℝ)
    (x₀ : EuclideanSpace ℝ I) (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 2 u)
    (hf : ContDiff ℝ 1 f)
    (hDA : HasLocalHolderBound α (fderiv ℝ A) x₀)
    (hHu : HasLocalHolderBound α (fderiv ℝ (fderiv ℝ u)) x₀)
    (hDf : HasLocalHolderBound α (fderiv ℝ f) x₀)
    (hPD : ∀ᶠ x in 𝓝 x₀, (A x).PosDef)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator A u x = f x) :
    ContDiffAt ℝ 3 u x₀ := by
  let L := OAI.Analysis.PDE.Dirichlet.coordinateReindex e.symm
  let P := OAI.Analysis.PDE.Dirichlet.coordinateReindex e
  let y₀ := P x₀
  have hLx : L y₀ = x₀ := OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x₀
  let B := fun y => OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm (A (L y))
  let v := u ∘ L
  let g := f ∘ L
  have hB : ContDiff ℝ 1 B := (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm).contDiff.comp (hA.comp L.contDiff)
  have hv : ContDiff ℝ 2 v := hu.comp L.contDiff
  have hg : ContDiff ℝ 1 g := hf.comp L.contDiff
  have hDB : HasLocalHolderBound α (fderiv ℝ B) y₀ := by
    exact localHolderBound_fderiv_linear_composition L (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm) A hA y₀
      (hLx ▸ hDA)
  have hDg : HasLocalHolderBound α (fderiv ℝ g) y₀ := by
    exact localHolderBound_fderiv_linear_composition L (ContinuousLinearMap.id ℝ ℝ) f hf y₀
      (hLx ▸ hDf)
  have hHv : HasLocalHolderBound α (fderiv ℝ (fderiv ℝ v)) y₀ := by
    obtain ⟨r, hr, C, hC, hh⟩ := hHu
    refine ⟨r, hr, C, hC, ?_⟩
    intro x hx y hy
    have hx' : L x ∈ ball x₀ r := by simpa only [mem_ball, ← hLx, L.dist_map] using hx
    have hy' : L y ∈ ball x₀ r := by simpa only [mem_ball, ← hLx, L.dist_map] using hy
    have hb := OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback L
      (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y)
      (fderiv ℝ (fderiv ℝ u) (L x) - fderiv ℝ (fderiv ℝ u) (L y)) (by
        intro a b
        simp only [sub_apply]
        apply congrArg₂ (· - ·)
        · exact OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between u hu L.toContinuousLinearEquiv.toContinuousLinearMap x a b
        · exact OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between u hu L.toContinuousLinearEquiv.toContinuousLinearMap y a b)
    apply hb.trans
    simpa only [← dist_eq_norm, L.dist_map] using hh (L x) hx' (L y) hy'
  have ht : Tendsto L (𝓝 y₀) (𝓝 x₀) := by simpa only [hLx] using L.continuous.tendsto y₀
  have hBP : ∀ᶠ y in 𝓝 y₀, (B y).PosDef := by
    filter_upwards [ht.eventually hPD] with y hy
    exact OAI.Analysis.PDE.Dirichlet.matrixReindex_posDef e.symm hy
  have hBeq : ∀ᶠ y in 𝓝 y₀, OAI.Analysis.PDE.Schauder.nondivergenceOperator B v y = g y := by
    filter_upwards [ht.eventually hPDE] with y hy
    exact (OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator_reindex e.symm A u hu y).trans hy
  have hc := linear_C3At_of_local_holder hm hα hα1 B v g y₀
    hB.contDiffAt hv.contDiffAt hg.contDiffAt hDB hHv hDg hBP hBeq
  have hvP : v ∘ P = u := by
    funext x
    exact congrArg u (OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x)
  have hh := hc.comp x₀ P.contDiff.contDiffAt
  rwa [hvP] at hh

end OAI.Analysis.PDE.Nonlinear
