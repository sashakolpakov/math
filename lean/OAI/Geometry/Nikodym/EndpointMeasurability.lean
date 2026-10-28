import OAI.Geometry.Nikodym.CompactCurveRestricted
import OAI.Geometry.Nikodym.EndpointFamily

noncomputable section
open Set Metric _root_.MeasureTheory
open scoped ENNReal
namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] [FiniteDimensional ℝ E] in
/-- Incidence with the geodesic segment and any closed endpoint constraint
form a closed admissible parameter family. In particular, exact prescribed
length and closed length windows are permitted. -/
theorem isClosed_endpoint_admissible (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target)
    {A : Set (EndpointParameters E r)} (hA : IsClosed A) :
    IsClosed {q : M × EndpointParameters E r |
      q.2∈A ∧ q.1∈range (endpointCurve H q.2)} := by
  have hc : Continuous (fun q : (M × EndpointParameters E r) × Icc (0 : ℝ) 1 =>
      endpointCurve H q.1.2 q.2) :=
    (continuous_endpointCurve H hr).comp (continuous_fst.snd.prodMk continuous_snd)
  exact (hA.preimage continuous_snd).inter (isClosed_compact_curve_incidence _ hc)

theorem measurable_endpoint_metric_maximal
    (μ : Measure M) (S : Set M) [IsFiniteMeasure (μ.restrict S)]
    (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) (δ : ℝ)
    (hz : ∀ ab : EndpointParameters E r,
      (μ.restrict S) {x | infDist x (range (endpointCurve H ab))=δ}=0)
    (hp : ∀ ab : EndpointParameters E r,
      (μ.restrict S) (metricTube δ (range (endpointCurve H ab))) ≠ 0)
    {A : Set (EndpointParameters E r)} (hA : IsClosed A)
    (f : M → ℂ) (hf : Integrable f (μ.restrict S)) :
    Measurable (metricTubeMaximal μ S (fun _ ab => range (endpointCurve H ab))
      (fun x ab => ab∈A ∧ x∈range (endpointCurve H ab)) δ f) := by
  let : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0,by norm_num⟩⟩
  have hc : Continuous (fun q : (M × EndpointParameters E r) × Icc (0 : ℝ) 1 =>
      endpointCurve H q.1.2 q.2) :=
    (continuous_endpointCurve H hr).comp (continuous_fst.snd.prodMk continuous_snd)
  exact measurable_metricTubeMaximal_of_compact_curves μ S _ hc δ
    (fun q => hz q.2) (fun q => hp q.2) _
    (isClosed_endpoint_admissible H hr hA) f hf

end OAI.Geometry.Nikodym
