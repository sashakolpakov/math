import OAI.Geometry.Nikodym.EndpointLength

noncomputable section
open Set Metric _root_.MeasureTheory

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def unitIntervalClamp (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem unitIntervalClamp_mem (t : ℝ) : unitIntervalClamp t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem unitIntervalClamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    unitIntervalClamp t = t := by
  simp only [unitIntervalClamp, min_eq_right ht.2, max_eq_right ht.1]

private def clampedSegmentSpeed (κ r : ℝ) (p : EndpointParameters E r) (t : ℝ) : ℝ :=
  beltramiSpeed κ
    (AffineMap.lineMap (p.1 : E) (p.2 : E) (unitIntervalClamp t))
    ((p.2 : E) - (p.1 : E))

omit [FiniteDimensional ℝ E] in
private theorem continuous_endpointSpeedPair (r : ℝ) :
    Continuous (fun q : EndpointParameters E r × ℝ =>
      (AffineMap.lineMap (q.1.1 : E) (q.1.2 : E) (unitIntervalClamp q.2),
        (q.1.2 : E) - (q.1.1 : E))) := by
  have ha : Continuous (fun q : EndpointParameters E r × ℝ => (q.1.1 : E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hb : Continuous (fun q : EndpointParameters E r × ℝ => (q.1.2 : E)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun q : EndpointParameters E r × ℝ => unitIntervalClamp q.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hl : Continuous (fun q : EndpointParameters E r × ℝ =>
      AffineMap.lineMap (q.1.1 : E) (q.1.2 : E) (unitIntervalClamp q.2)) := by
    simpa only [AffineMap.lineMap_apply_module] using!
      (((continuous_const.sub ht).smul ha).add (ht.smul hb))
  exact hl.prodMk (hb.sub ha)

omit [FiniteDimensional ℝ E] in
private theorem clampedSegmentDenominator_ne {κ r : ℝ}
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) :
    ∀ q : EndpointParameters E r × ℝ, beltramiDenominator κ
      (AffineMap.lineMap (q.1.1 : E) (q.1.2 : E) (unitIntervalClamp q.2)) ≠ 0 := by
  intro q
  have hmem := (convex_closedBall (0 : E) r).lineMap_mem
    q.1.1.property q.1.2.property (unitIntervalClamp_mem q.2)
  have hden := (beltramiDenominator_small (hsmall _ hmem)).1
  linarith

omit [FiniteDimensional ℝ E] in
private theorem continuous_speed_comp {P : Type*} [TopologicalSpace P]
    (κ : ℝ) (f : P → E × E) (hf : Continuous f)
    (hne : ∀ p, beltramiDenominator κ (f p).1 ≠ 0) :
    Continuous (fun p => beltramiSpeed κ (f p).1 (f p).2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (continuousAt_beltramiSpeed κ (hne p)).comp hf.continuousAt

omit [FiniteDimensional ℝ E] in
private theorem continuous_clampedSegmentSpeed {κ r : ℝ}
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) :
    Continuous (clampedSegmentSpeed (E := E) κ r).uncurry := by
  exact continuous_speed_comp κ
    (fun q : EndpointParameters E r × ℝ =>
      (AffineMap.lineMap (q.1.1 : E) (q.1.2 : E) (unitIntervalClamp q.2),
        (q.1.2 : E) - (q.1.1 : E)))
    (continuous_endpointSpeedPair r) (clampedSegmentDenominator_ne hsmall)

/-- Joint endpoint continuity of the actual speed integral.  Clamping the
integration parameter extends the integrand continuously without evaluating
the metric beyond the small coordinate ball. -/
theorem continuous_beltramiSegmentLength_endpoints {κ r : ℝ}
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) :
    Continuous (fun p : EndpointParameters E r =>
      beltramiSegmentLength κ (p.1 : E) (p.2 : E)) := by
  have H : Continuous (fun p : EndpointParameters E r =>
      ∫ t in Icc (0 : ℝ) 1, clampedSegmentSpeed κ r p t) :=
    continuous_parametric_integral_of_continuous (E := ℝ)
      (continuous_clampedSegmentSpeed hsmall) isCompact_Icc
  convert H using 1
  funext p
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [clampedSegmentSpeed, unitIntervalClamp_eq ht]

/-- Prescribing an actual Riemannian segment length is a closed endpoint
constraint; it is not replaced by a Euclidean endpoint-distance condition. -/
theorem isClosed_fixed_beltramiSegmentLength {κ r : ℝ}
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) (ell : ℝ) :
    IsClosed {p : EndpointParameters E r |
      beltramiSegmentLength κ (p.1 : E) (p.2 : E) = ell} :=
  isClosed_eq (continuous_beltramiSegmentLength_endpoints hsmall) continuous_const

theorem isCompact_fixed_beltramiSegmentLength {κ r : ℝ}
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) (ell : ℝ) :
    IsCompact {p : EndpointParameters E r |
      beltramiSegmentLength κ (p.1 : E) (p.2 : E) = ell} :=
  (isClosed_fixed_beltramiSegmentLength hsmall ell).isCompact

end OAI.Geometry.Nikodym
