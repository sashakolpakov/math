import OAI.Geometry.Nikodym.Beltrami.Reparam
import OAI.Geometry.Nikodym.Abstract.InverseGeodesic
import OAI.Geometry.Nikodym.SegmentReparamLength
import OAI.Geometry.Nikodym.PositiveTimeChange
import OAI.Geometry.Nikodym.SegmentNeighborhood

noncomputable section
open Set Bundle Manifold
open scoped Topology ContDiff Bundle ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

/-- Every inverse chart segment is the image of an actual affinely
parametrized Riemannian geodesic. Its actual ambient length is exactly
the endpoint integral used to index the segment maximal operator. -/
theorem exists_inverse_segment_geodesic {a b : E}
    (hseg : segment ℝ a b ⊆ C.manifoldChart.target) :
    ∃ (γ : ℝ → M) (v : ℝ → E) (I : Set ℝ) (T : ℝ),
      IsOpen I ∧ IsPreconnected I ∧ 0 < T ∧ Icc 0 T ⊆ I ∧
      IsAtlasGeodesic p γ v I ∧ MapsTo γ I C.manifoldChart.source ∧
      γ '' Icc 0 T = C.manifoldChart.symm '' segment ℝ a b ∧
      pathELength 𝓘(ℝ,E) γ 0 T = ENNReal.ofReal (beltramiSegmentLength κ a b) := by
  obtain ⟨l,r,hl,hr,hline⟩ := segment_open_parameter_extension
    C.manifoldChart.open_target hseg
  let q : ℝ → ℝ := fun s => beltramiDenominator κ (AffineMap.lineMap a b s)
  have hq : Continuous q := by
    exact continuous_const.add (continuous_const.mul (AffineMap.lineMap_continuous.norm.pow 2))
  have hqpos (s : ℝ) (hs : s ∈ Ioo l r) : 0 < q s := by
    have hy := hline hs
    have hp := C.manifoldChart_positive (C.manifoldChart.map_target hy)
    simpa only [C.manifoldChart.right_inv hy] using hp
  obtain ⟨T,hsource,-,hzero,hmono,-,hinverse,hconn,hT,hsub,himage⟩ :=
    exists_positive_timeChange hq hl hr hqpos
  let γ₀ : ℝ → E := AffineMap.lineMap a b ∘ T.symm
  let v₀ : ℝ → E := fun t => q (T.symm t) • (b-a)
  have hin (t : ℝ) (ht : t ∈ T.target) : γ₀ t ∈ C.manifoldChart.target := by
    exact hline (hsource ▸ T.map_target ht)
  have hgeo : IsBeltramiGeodesic κ γ₀ v₀ T.target :=
    isBeltramiGeodesic_line_reparam a b hinverse
      (fun t ht => hqpos _ (hsource ▸ T.map_target ht))
  have hs0 : T.symm 0 = 0 := by
    have hh : (0 : ℝ) ∈ T.source := by rw [hsource]; exact ⟨hl,by linarith⟩
    simpa only [hzero] using T.left_inv hh
  have hs1 : T.symm (T 1) = 1 := by
    apply T.left_inv
    rw [hsource]
    exact ⟨by linarith,hr⟩
  have hmonoinv : MonotoneOn T.symm (Icc 0 (T 1)) := by
    intro x hx y hy hxy
    apply le_of_not_gt
    intro hbad
    have hb := hmono (T.map_target (hsub hy)) (T.map_target (hsub hx)) hbad
    rw [T.right_inv (hsub hy),T.right_inv (hsub hx)] at hb
    exact (not_lt_of_ge hxy) hb
  refine ⟨C.manifoldChart.symm ∘ γ₀,
    fun t => fderiv ℝ (C.chart.symm : E → E) (γ₀ t) (v₀ t),
    T.target,T 1,T.open_target,hconn.isPreconnected,hT,hsub,
    C.inverse_atlasGeodesic hgeo T.open_target hin,?_,?_,?_⟩
  · exact fun t ht => C.manifoldChart.map_target (hin t ht)
  · rw [image_comp]
    exact congrArg (fun A : Set E => C.manifoldChart.symm '' A) (line_reparam_image himage)
  · exact C.pathELength_inverse_segment_reparam hseg hT.le hmonoinv
      (fun t ht => (hinverse t (hsub ht)).differentiableAt.differentiableWithinAt) hs0 hs1

end OAI.Geometry.Nikodym.LocalBeltramiChart
