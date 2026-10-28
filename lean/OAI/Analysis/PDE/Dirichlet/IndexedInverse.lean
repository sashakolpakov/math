import OAI.Analysis.PDE.Dirichlet.MatrixTransport
import OAI.Analysis.Normed.Function.Holder.C2HolderIsometryMap
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixInverse

open Set Metric
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ} {α R : ℝ}

local instance indexedFullNormedGroup : NormedAddCommGroup
    (OAI.Analysis.Normed.Function.Holder.FullSpaceC2 (EuclideanSpace ℝ I) α) := inferInstance
local instance indexedFullNormedSpace : NormedSpace ℝ
    (OAI.Analysis.Normed.Function.Holder.FullSpaceC2 (EuclideanSpace ℝ I) α) := inferInstance
local instance indexedGlobalNormedGroup : NormedAddCommGroup (OAI.Analysis.PDE.Schauder.GlobalC2Holder m α) := inferInstance
local instance indexedGlobalNormedSpace : NormedSpace ℝ (OAI.Analysis.PDE.Schauder.GlobalC2Holder m α) := inferInstance
local instance indexedSupportedNormedGroup : NormedAddCommGroup (OAI.Analysis.PDE.Schauder.SupportedHolder m α R) :=
  inferInstance
local instance indexedSupportedNormedSpace : NormedSpace ℝ (OAI.Analysis.PDE.Schauder.SupportedHolder m α R) :=
  inferInstance

theorem coefficientReindex_one_sub (hα : 0 ≤ α) (e : I ≃ Fin m)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (Matrix I I ℝ) α) :
    (fun y i j ↦ (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e.symm B)
      (coordinateReindex e y)) (e i) (e j)) = (fun y ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) := by
  funext y i j
  simp only [Matrix.sub_apply, Matrix.one_apply, coefficientReindex_apply,
    coordinateReindex_symm_apply, Equiv.symm_apply_apply, e.injective.eq_iff]

def supportedReindex (hα : 0 ≤ α) (e : I ≃ Fin m)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α)
    (hf : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0) : OAI.Analysis.PDE.Schauder.SupportedHolder m α R :=
  ⟨OAI.Analysis.PDE.Schauder.holderIsometricPullback hα (coordinateReindex e.symm) (coordinateReindex e.symm).isometry f,
    fun x hx ↦ hf (coordinateReindex e.symm x) (by
      simpa only [mem_closedBall, dist_zero_right, (coordinateReindex e.symm).norm_map] using hx)⟩

omit [DecidableEq I] in
theorem norm_supportedReindex_le (hα : 0 ≤ α) (e : I ≃ Fin m)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α)
    (hf : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0) :
    ‖supportedReindex hα e f hf‖ ≤ ‖f‖ :=
  OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα (coordinateReindex e.symm)
    (coordinateReindex e.symm).isometry f

theorem indexed_equation_pullback (hα : 0 ≤ α) (e : I ≃ Fin m)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (Matrix I I ℝ) α)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α)
    (hf : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0)
    (v : OAI.Analysis.PDE.Schauder.GlobalC2Holder m α)
    (hv : ∀ y, OAI.Analysis.PDE.Schauder.nondivergenceOperator
      (fun z ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e.symm B) z)
      (OAI.Analysis.PDE.Schauder.globalC2Value v) y = OAI.Analysis.PDE.Schauder.SupportedHolder.value (supportedReindex hα e f hf) y)
    (u : OAI.Analysis.Normed.Function.Holder.FullSpaceC2 (EuclideanSpace ℝ I) α)
    (hu : OAI.Analysis.Normed.Function.Holder.fullValue u = OAI.Analysis.Normed.Function.Holder.fullValue v ∘ coordinateReindex e) (x : EuclideanSpace ℝ I) :
    indexedNondivergenceOperator (fun y ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) (OAI.Analysis.Normed.Function.Holder.fullValue u) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value f x := by
  have ht := indexedNondivergenceOperator_reindex e
    (fun y ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e.symm B) y)
    (OAI.Analysis.Normed.Function.Holder.fullValue v) (OAI.Analysis.Normed.Function.Holder.contDiff_fullValue v) x
  rw [coefficientReindex_one_sub hα e B] at ht
  rw [hu]
  calc
    _ = indexedNondivergenceOperator
        (fun y ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e.symm B) y)
        (OAI.Analysis.Normed.Function.Holder.fullValue v) (coordinateReindex e x) := ht
    _ = OAI.Analysis.PDE.Schauder.SupportedHolder.value (supportedReindex hα e f hf) (coordinateReindex e x) :=
      hv (coordinateReindex e x)
    _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value f x := by
      change OAI.Analysis.Normed.Function.Holder.HolderMap.value f (coordinateReindex e.symm (coordinateReindex e x)) = _
      rw [coordinateReindex_symm_apply]

/-- The actual small-coefficient inverse in any finite coordinate system.
This transports both the PDE and the complete C²,α solution space. -/
theorem indexed_small_coefficient_inverse (e : I ≃ Fin m) (hm : 3 ≤ m)
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (Matrix I I ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖OAI.Analysis.PDE.Schauder.poissonHolderOperator hm hα hα1 R‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α,
      (∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0) →
      ∃ u : OAI.Analysis.Normed.Function.Holder.FullSpaceC2 (EuclideanSpace ℝ I) α,
        ‖u‖ ≤ C * ‖f‖ ∧ ∀ x,
          indexedNondivergenceOperator (fun y ↦ 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) (OAI.Analysis.Normed.Function.Holder.fullValue u) x =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value f x := by
  let B' := coefficientReindex hα.le e.symm B
  have hB' : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B' x = 0 :=
    coefficientReindex_supported hα.le e.symm B hB
  have hsmall' : 2 * ((m : ℝ) * m * ‖B'‖) * ‖OAI.Analysis.PDE.Schauder.poissonHolderOperator hm hα hα1 R‖ < 1 := by
    apply lt_of_le_of_lt _ hsmall
    gcongr
    exact norm_coefficientReindex_le hα.le e.symm B
  let T := OAI.Analysis.PDE.Schauder.smallMatrixSolutionOperator hm hα hα1 B' hB' hsmall'
  refine ⟨‖T‖, norm_nonneg T, ?_⟩
  intro f hf
  let f' := supportedReindex hα.le e f hf
  have hfNorm : ‖f'‖ ≤ ‖f‖ := norm_supportedReindex_le hα.le e f hf
  obtain ⟨u, hu, hnorm⟩ := OAI.Analysis.Normed.Function.Holder.exists_fullSpace_pullback hα.le (coordinateReindex e) (T f')
  refine ⟨u, hnorm.trans ((T.le_opNorm f').trans
    (mul_le_mul_of_nonneg_left hfNorm (norm_nonneg T))), ?_⟩
  exact indexed_equation_pullback hα.le e B f hf (T f')
    (OAI.Analysis.PDE.Schauder.smallMatrixSolutionOperator_solves hm hα hα1 B' hB' hsmall' f') u hu

end OAI.Analysis.PDE.Dirichlet
