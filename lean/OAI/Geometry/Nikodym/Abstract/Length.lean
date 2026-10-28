import OAI.Geometry.Nikodym.Abstract.ChartMetric
import OAI.Geometry.Nikodym.Beltrami.Length
import Mathlib.Geometry.Manifold.Riemannian.PathELength

noncomputable section
open Set Bundle Manifold Filter _root_.MeasureTheory
open scoped Topology ContDiff Bundle RealInnerProductSpace ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

theorem manifoldChart_inverse_speed {y : E} (hy : y ∈ C.manifoldChart.target) (v : E) :
    ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.manifoldChart.symm y v‖ = beltramiSpeed κ y v := by
  rw [norm_eq_sqrt_real_inner,C.manifoldChart_inverse_metric hy]
  rfl

theorem manifoldChart_inverse_curve_derivative {γ v : ℝ → E} {t : ℝ}
    (hγ : HasDerivAt γ (v t) t) (ht : γ t ∈ C.manifoldChart.target) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ,E) (C.manifoldChart.symm ∘ γ) t 1 =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.manifoldChart.symm (γ t) (v t) := by
  have hi := ((C.manifoldChart_inverse_smooth _ ht).contMDiffAt
    (C.manifoldChart.open_target.mem_nhds ht)).mdifferentiableAt (by simp)
  have hv : mfderiv 𝓘(ℝ) 𝓘(ℝ,E) γ t 1 = v t := by
    have hf : fderiv ℝ γ t 1 = v t := by
      rw [hγ.hasFDerivAt.fderiv]
      exact one_smul ℝ (v t)
    simpa only [mfderiv_eq_fderiv] using! hf
  have hd := mfderiv_comp_apply t hi hγ.differentiableAt.mdifferentiableAt (1 : ℝ)
  exact hd.trans (congrArg (fun w : E =>
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.manifoldChart.symm (γ t) w) hv)

/-- The model length is the actual ambient Riemannian path length,
not the distance intrinsic to an artificially restricted chart. -/
theorem pathELength_manifoldChart_inverse {γ v : ℝ → E} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (v t) t)
    (ht : MapsTo γ (Icc a b) C.manifoldChart.target) :
    pathELength 𝓘(ℝ,E) (C.manifoldChart.symm ∘ γ) a b =
      beltramiPathLength κ γ v a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc,beltramiPathLength]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht'
  have hn : ‖mfderiv 𝓘(ℝ) 𝓘(ℝ,E) (C.manifoldChart.symm ∘ γ) t 1‖ =
      beltramiSpeed κ (γ t) (v t) :=
    (congrArg norm (C.manifoldChart_inverse_curve_derivative (hγ t ht') (ht ht'))).trans
      (C.manifoldChart_inverse_speed (ht ht') (v t))
  exact (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal hn)

theorem pathELength_manifoldCurve {γ : ℝ → M} {v : ℝ → E} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt (C.manifoldChart ∘ γ) (v t) t)
    (ht : MapsTo γ (Icc a b) C.manifoldChart.source) :
    pathELength 𝓘(ℝ,E) γ a b =
      beltramiPathLength κ (C.manifoldChart ∘ γ) v a b := by
  have he : EqOn (C.manifoldChart.symm ∘ (C.manifoldChart ∘ γ)) γ (Icc a b) := by
    intro t ht'
    exact C.manifoldChart.left_inv (ht ht')
  have hl := pathELength_congr (I:=𝓘(ℝ,E)) he
  exact hl.symm.trans (C.pathELength_manifoldChart_inverse hγ
    (fun t ht' => C.manifoldChart.map_source (ht ht')))

end OAI.Geometry.Nikodym.LocalBeltramiChart
