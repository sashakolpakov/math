import OAI.Geometry.Nikodym.BorelChart

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Metric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]

abbrev EndpointParameters (E : Type*) [PseudoMetricSpace E] [Zero E] (r : ℝ) :=
  Metric.closedBall (0 : E) r × Metric.closedBall (0 : E) r

def endpointCurve (H : OpenPartialHomeomorph M E) {r : ℝ}
    (ab : EndpointParameters E r) (t : Icc (0 : ℝ) 1) : M :=
  H.symm (AffineMap.lineMap (ab.1 : E) (ab.2 : E) (t : ℝ))

omit [FiniteDimensional ℝ E] in
theorem continuous_endpointCurve (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) :
    Continuous (fun q : EndpointParameters E r × Icc (0 : ℝ) 1 =>
      endpointCurve H q.1 q.2) := by
  have hc : Continuous (fun q : EndpointParameters E r × Icc (0 : ℝ) 1 =>
      AffineMap.lineMap (q.1.1 : E) (q.1.2 : E) (q.2 : ℝ)) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  apply H.symm.continuousOn.comp_continuous hc
  intro q
  exact hr ((convex_closedBall (0 : E) r).lineMap_mem q.1.1.property
    q.1.2.property q.2.property)

omit [FiniteDimensional ℝ E] in
theorem endpointCurve_mem_source (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) (ab : EndpointParameters E r)
    (t : Icc (0 : ℝ) 1) : endpointCurve H ab t ∈ H.source :=
  H.map_target (hr ((convex_closedBall (0 : E) r).lineMap_mem ab.1.property
    ab.2.property t.property))

omit [FiniteDimensional ℝ E] in
theorem chart_endpointCurve (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) (ab : EndpointParameters E r)
    (t : Icc (0 : ℝ) 1) :
    H (endpointCurve H ab t) = AffineMap.lineMap (ab.1 : E) (ab.2 : E) (t : ℝ) :=
  H.right_inv (hr ((convex_closedBall (0 : E) r).lineMap_mem ab.1.property
    ab.2.property t.property))

omit [FiniteDimensional ℝ E] in
theorem isCompact_endpointCurve_range (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) (ab : EndpointParameters E r) :
    IsCompact (range (endpointCurve H ab)) := by
  apply isCompact_range
  exact (continuous_endpointCurve H hr).comp (continuous_const.prodMk continuous_id)

omit [FiniteDimensional ℝ E] in
theorem endpointCurve_range_subset (H : OpenPartialHomeomorph M E) {r : ℝ}
    (ab : EndpointParameters E r) :
    range (endpointCurve H ab) ⊆ H.symm '' closedBall (0 : E) r := by
  rintro x ⟨t,rfl⟩
  exact ⟨_,(convex_closedBall (0 : E) r).lineMap_mem ab.1.property ab.2.property t.property,rfl⟩

omit [FiniteDimensional ℝ E] in
theorem chart_endpointCurve_range (H : OpenPartialHomeomorph M E) {r : ℝ}
    (hr : closedBall (0 : E) r ⊆ H.target) (ab : EndpointParameters E r) :
    H '' range (endpointCurve H ab) = segment ℝ (ab.1 : E) (ab.2 : E) := by
  rw [segment_eq_image']
  ext y
  constructor
  · rintro ⟨x,⟨t,rfl⟩,rfl⟩
    refine ⟨t,t.property,?_⟩
    rw [chart_endpointCurve H hr]
    simp only [AffineMap.lineMap_apply_module]
    module
  · rintro ⟨t,ht,rfl⟩
    refine ⟨endpointCurve H ab ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,?_⟩
    rw [chart_endpointCurve H hr]
    simp only [AffineMap.lineMap_apply_module]
    module

end OAI.Geometry.Nikodym
