import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentChart

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Dirichlet

variable {E I P₀ V₀ ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype I]
  [NormedAddCommGroup P₀] [NormedSpace ℝ P₀]
  [NormedAddCommGroup V₀] [NormedSpace ℝ V₀] [Fintype ι]

/-- An arbitrary smooth field can be periodized without changing its germ.
There is no tangency assertion for this extension. -/
theorem exists_latticePeriodic_field_extension
    (e : E ≃L[ℝ] P₀ × V₀) (lat : Basis ι ℝ P₀)
    (a : E) (f : E → E) (hf : ContDiff ℝ ∞ f) :
    ∃ T : E → E, ContDiff ℝ ∞ T ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat T ∧
      ∃ O : Set E, IsOpen O ∧ a ∈ O ∧ EqOn T f O := by
  obtain ⟨T,hT,hTp,_,O,hO,haO,_,heq⟩ :=
    exists_latticePeriodic_tangent_extension e lat (fun _ => (-1 : ℝ))
      (fun _ _ => rfl) isOpen_univ (mem_univ a) f hf (by
        intro x hx hz
        norm_num at hz)
  exact ⟨T,hT,hTp,O,hO,haO,heq⟩

/-- Periodize any direction tangent to a flattened boundary in an arbitrary
physical inner product space, rather than only in a coordinate model. -/
theorem exists_latticePeriodic_linear_level_tangent
    (e : E ≃L[ℝ] P₀ × V₀) (lat : Basis ι ℝ P₀) {r : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    {G P : E → E} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : E} (hG0 : G 0 = a) (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (ℓ : E →L[ℝ] ℝ) (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = ℓ z)
    (v : E) (hv : ℓ v = 0) :
    ∃ T : E → E, ContDiff ℝ ∞ T ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat T ∧
      (∀ x, r x = 0 → fderiv ℝ r x (T x) = 0) ∧
      ∃ O : Set E, IsOpen O ∧ a ∈ O ∧ EqOn T (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) O := by
  obtain ⟨_,R,hR,U,hU,haU,hRU,hGP,hPU⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood (hP.of_le (by simp)) (hG.of_le (by simp))
      hG0 hinv (show (0 : ℝ) < 1 by norm_num)
  have ht := chartTangentField_tangent_of_linear_level
    (hG.differentiable (by simp)) (hr.differentiable (by simp)) isOpen_ball hPU hGP
    ℓ (r a) (by
      intro z hz
      have hz2 : z ∈ closedBall (0 : E) 2 :=
        ball_subset_closedBall ((ball_subset_ball (show (1 : ℝ) ≤ 2 by norm_num)) hz)
      have he := hlevel z hz2
      linarith) v hv
  obtain ⟨T,hT,hTp,hTtan,O,hO,haO,_,heq⟩ :=
    exists_latticePeriodic_tangent_extension e lat r hrp hU haU
      (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) (contDiff_chartTangentField_infty hG hP v)
      (fun x hx _ => ht x hx)
  exact ⟨T,hT,hTp,hTtan,O,hO,haO,heq⟩

/-- A finite coordinate frame has simultaneous periodic extensions on a
fixed closed chart ball. All but the distinguished normal direction are
globally tangent; the normal extension is still available for the PDE. -/
theorem exists_latticePeriodic_chart_frame
    (e : E ≃L[ℝ] P₀ × V₀) (lat : Basis ι ℝ P₀) {r : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    {G P : E → E} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : E} (hG0 : G 0 = a) (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (ℓ : E →L[ℝ] ℝ) (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = ℓ z)
    (k : I) (v : I → E) (hv : ∀ i, i ≠ k → ℓ (v i) = 0) :
    ∃ δ > 0, δ < 1 ∧ ∃ T : I → E → E,
      (∀ i, ContDiff ℝ ∞ (T i)) ∧ (∀ i, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (T i)) ∧
      (∀ i, i ≠ k → ∀ x, r x = 0 → fderiv ℝ r x (T i x) = 0) ∧
      (∀ i z, z ∈ closedBall 0 δ →
        T i =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G P (v i)) := by
  classical
  have hex (i : I) : ∃ T : E → E, ContDiff ℝ ∞ T ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat T ∧
      (i ≠ k → ∀ x, r x = 0 → fderiv ℝ r x (T x) = 0) ∧
      ∃ O : Set E, IsOpen O ∧ a ∈ O ∧ EqOn T (OAI.Analysis.PDE.Elliptic.chartTangentField G P (v i)) O := by
    by_cases hik : i = k
    · obtain ⟨T,hT,hTp,O,hO,haO,heq⟩ := exists_latticePeriodic_field_extension e lat a
        (OAI.Analysis.PDE.Elliptic.chartTangentField G P (v i)) (contDiff_chartTangentField_infty hG hP (v i))
      exact ⟨T,hT,hTp,fun h => (h hik).elim,O,hO,haO,heq⟩
    · obtain ⟨T,hT,hTp,hTtan,O,hO,haO,heq⟩ :=
        exists_latticePeriodic_linear_level_tangent e lat hr hrp hG hP hG0 hinv
          ℓ hlevel (v i) (hv i hik)
      exact ⟨T,hT,hTp,fun _ => hTtan,O,hO,haO,heq⟩
  choose T hT hTp hTtan O hO haO hTO using hex
  let W := G ⁻¹' (⋂ i, O i)
  have hW : IsOpen W := (isOpen_iInter_of_finite hO).preimage hG.continuous
  have h0W : (0 : E) ∈ W := by
    change G 0 ∈ ⋂ i, O i
    rw [hG0]
    exact mem_iInter.mpr haO
  obtain ⟨ε,hε,hεW⟩ := Metric.isOpen_iff.mp hW 0 h0W
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ,hδ,hδ1,T,hT,hTp,hTtan,?_⟩
  intro i z hz
  have hzW : z ∈ W := hεW (lt_of_le_of_lt hz hδε)
  have hzi : G z ∈ O i := mem_iInter.mp hzW i
  filter_upwards [(hO i).mem_nhds hzi] with y hy
  exact hTO i hy

end OAI.Analysis.Calculus.SmoothExtension
