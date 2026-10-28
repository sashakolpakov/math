import OAI.Geometry.Nikodym.GeodesicParameter
import OAI.Geometry.Nikodym.Abstract.Geodesic
import OAI.Geometry.Nikodym.Abstract.EndpointLength

noncomputable section
open Set Bundle Manifold Filter _root_.MeasureTheory
open scoped ContDiff Topology ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

theorem atlasGeodesic_to_model {γ : ℝ → M} {v : ℝ → E} {I : Set ℝ}
    (hγ : IsAtlasGeodesic p γ v I) (hinside : MapsTo γ I C.manifoldChart.source) :
    IsBeltramiGeodesic κ (C.manifoldChart ∘ γ)
      (fun t => fderiv ℝ (C.chart : E → E) (extChartAt 𝓘(ℝ,E) p (γ t)) (v t)) I := by
  exact hγ.equation.map_beltrami
    (fun t ht => C.positive _ (hinside ht).2)
    (fun t ht => ((C.smooth _ (hinside ht).2).contDiffAt
      (C.chart.open_source.mem_nhds (hinside ht).2)).of_le (by simp))
    (by
      intro t ht
      filter_upwards [C.chart.open_source.mem_nhds (hinside ht).2] with y hy
      exact C.metric y hy)

theorem atlasGeodesic_image_eq_segment {γ : ℝ → M} {v : ℝ → E} {I : Set ℝ}
    (hγ : IsAtlasGeodesic p γ v I) (hinside : MapsTo γ I C.manifoldChart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ I) :
    C.manifoldChart '' (γ '' Icc a b) =
      segment ℝ (C.manifoldChart (γ a)) (C.manifoldChart (γ b)) := by
  rw [← image_comp]
  exact (C.atlasGeodesic_to_model hγ hinside).segment_image_of_le hI hconn hab hsub

/-- The length of an arbitrary nontrivial atlas geodesic is exactly the
Riemannian length of its endpoint segment in the model coordinates. This
uses an actual monotone reparameterization and ambient path-length invariance. -/
theorem atlasGeodesic_length_eq {γ : ℝ → M} {v : ℝ → E} {I : Set ℝ}
    (hγ : IsAtlasGeodesic p γ v I) (hinside : MapsTo γ I C.manifoldChart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ I) (hpos : 0 < pathELength 𝓘(ℝ,E) γ a b) :
    pathELength 𝓘(ℝ,E) γ a b = ENNReal.ofReal
      (beltramiSegmentLength κ (C.manifoldChart (γ a)) (C.manifoldChart (γ b))) := by
  let ψ : ℝ → E := C.manifoldChart ∘ γ
  let w : ℝ → E := fun t => fderiv ℝ (C.chart : E → E)
    (extChartAt 𝓘(ℝ,E) p (γ t)) (v t)
  have hm : IsBeltramiGeodesic κ ψ w I := C.atlasGeodesic_to_model hγ hinside
  have ha : a ∈ I := hsub (left_mem_Icc.mpr hab.le)
  have hw : w a ≠ 0 := by
    intro hz
    have he : EqOn γ (fun _ => γ a) (Icc a b) := by
      intro t ht
      apply C.manifoldChart.injOn (hinside (hsub ht)) (hinside ha)
      exact hm.constant_of_zero_velocity hI hconn ha hz t (hsub ht)
    have hlen := pathELength_congr (I:=𝓘(ℝ,E)) he
    rw [hlen] at hpos
    simp [pathELength_eq_lintegral_mfderiv_Icc] at hpos
  obtain ⟨θ,hθa,hθb,hmono,hdiff,he⟩ :=
    hm.monotone_endpoint_parameter hI hconn hab hsub hw
  have hseg : segment ℝ (ψ a) (ψ b) ⊆ C.manifoldChart.target := by
    rw [← hm.segment_image hI hconn hab.le hsub hw]
    rintro y ⟨t,ht,rfl⟩
    exact C.manifoldChart.map_source (hinside (hsub ht))
  let F : ℝ → M := C.manifoldChart.symm ∘ AffineMap.lineMap (ψ a) (ψ b)
  have hF : MDifferentiableOn 𝓘(ℝ) 𝓘(ℝ,E) F (Icc (0 : ℝ) 1) := by
    apply (C.manifoldChart_inverse_smooth.mdifferentiableOn (by simp)).comp
    · have hc : ContDiff ℝ ∞ (AffineMap.lineMap (ψ a) (ψ b) : ℝ → E) := by
        simpa only [ContinuousAffineMap.coe_lineMap_eq] using
          (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R:=ℝ) (ψ a) (ψ b)))
      exact (hc.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
    · intro t ht
      apply hseg
      rw [segment_eq_image']
      refine ⟨t,ht,?_⟩
      simp only [AffineMap.lineMap_apply_module]
      module
  have he' : EqOn γ (F ∘ θ) (Icc a b) := by
    intro t ht
    change γ t = C.manifoldChart.symm (AffineMap.lineMap (ψ a) (ψ b) (θ t))
    have het : ψ t = AffineMap.lineMap (ψ a) (ψ b) (θ t) := he ht
    rw [← het]
    exact (C.manifoldChart.left_inv (hinside (hsub ht))).symm
  rw [pathELength_congr (I:=𝓘(ℝ,E)) he']
  have hF' : MDifferentiableOn 𝓘(ℝ) 𝓘(ℝ,E) F (Icc (θ a) (θ b)) := by
    rwa [hθa,hθb]
  rw [pathELength_comp_of_monotoneOn hab.le hmono hdiff hF',hθa,hθb]
  exact C.pathELength_inverse_segment hseg

end OAI.Geometry.Nikodym.LocalBeltramiChart
