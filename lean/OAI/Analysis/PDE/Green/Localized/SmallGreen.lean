import OAI.Analysis.PDE.Green.Localized.FluxCoordinates
import OAI.Analysis.PDE.Green.Localized.Green
import OAI.Analysis.PDE.Green.SmallGreen

/-! The quantitative Green estimate with boundary data localized to the test. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem realFlux_divergence_at
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (d : I → E) (K : I → I → E → ℝ) {v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j)) (hv : ContDiff ℝ 2 v) (x : E)
    (hdiv : ∀ j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) :
    (∑ i, fderiv ℝ (realFlux d K v i) x (d i)) =
      ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j) := by
  simp_rw [fderiv_realFlux d K hK hv, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => fderiv ℝ (K i j) x (d i) * fderiv ℝ v x (d j))]
  simp only [← Finset.sum_mul, hdiv, zero_mul, Finset.sum_const_zero, zero_add]

theorem real_operator_second_green_localized_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (∀ j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hboundary : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖normalRealFlux (fun i => EuclideanSpace.single i 1) K r u y‖ ≤ ε) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hface : CompatibleCellFaces c a b r
      (secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    ‖(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) -
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))‖ ≤ ε * W := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hq₀ : ContDiff ℝ 1 (fun x => -normalRealFlux d K r u x) :=
    (contDiff_normalRealFlux d K hK hr hu).neg
  have hq₁ : ContDiff ℝ 1 (fun x => u x * normalRealFlux d K r v x) :=
    (hu.of_le (by norm_num)).mul (contDiff_normalRealFlux d K hK hr hv)
  have hloc : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧
        (∀ᶠ y in 𝓝 x, r y = 0 → ‖-normalRealFlux d K r u y‖ ≤ ε) ∧
        (∀ᶠ y in 𝓝 x, r y = 0 → u y * normalRealFlux d K r v y = 0)) ∨
      (v =ᶠ[𝓝 x] (fun _ => 0)) ∧
      ((fun y => u y * normalRealFlux d K r v y) =ᶠ[𝓝 x] (fun _ => 0)) := by
    intro x hx hrx
    rcases hboundary x hx hrx with ⟨hreg, hlocal⟩ | hz
    · refine Or.inl ⟨hreg, ?_, ?_⟩
      · filter_upwards [hlocal] with y hy hyr
        simpa only [norm_neg] using (hy hyr).2
      · filter_upwards [hlocal] with y hy hyr
        simp only [(hy hyr).1, zero_mul]
    · refine Or.inr ⟨hz, ?_⟩
      filter_upwards [hz, secondGreenFlux_eventually_zero d K u v x hz] with y hyv hyF
      have hh := secondGreenFlux_normal_decomposition d K r u v y
      simp only [hyF, mul_zero, Finset.sum_const_zero, hyv, zero_mul, zero_add] at hh
      exact hh.symm
  have hcompact : IsCompact (euclideanCoordinates c ⁻¹' Icc a b) :=
    (euclideanCoordinates c).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  obtain ⟨C, hC, hbound⟩ := localized_product_boundary_bound hcompact
    (hr.of_le (by norm_num)) hq₀ hq₁ hv.continuous hε hloc
  have he := euclidean_weighted_divergence_of_normal_bound c a b hab
    (secondGreenFlux d K u v) (contDiff_secondGreenFlux d K hK hu hv)
    (hr.of_le (by norm_num)) hv.continuous hε hW
    (fun x hx => by
      rw [secondGreenFlux_normal_decomposition]
      exact hbound x hx) hface
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (realFlux d K v i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (contDiff_realFlux d K hK hv i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (realFlux d K u i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (contDiff_realFlux d K hK hu i) (d i))))
  change ‖∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (secondGreenFlux d K u v i) x (d i)‖ ≤ ε * W at he
  simp_rw [secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have hS : MeasurableSet ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    (isClosed_Icc.preimage (euclideanCoordinates c).continuous).measurableSet.inter
      (isOpen_lt hr.continuous continuous_const).measurableSet
  have hvEq : (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      u x * ∑ i, fderiv ℝ (realFlux d K v i) x (d i)) =
      ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        u x * ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j) := by
    apply setIntegral_congr_fun hS
    intro x hx
    rcases hdiv x hx with hd | hz
    · exact congrArg (fun t : ℝ => u x * t) (realFlux_divergence_at d K hK hv x hd)
    · have hfirst : fderiv ℝ v x = 0 := by simpa using hz.fderiv_eq (𝕜 := ℝ)
      have hsecond : fderiv ℝ (fderiv ℝ v) x = 0 := by
        simpa using (hz.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
      simp [fderiv_realFlux d K hK hv, hfirst, hsecond]
  have huEq : (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      v x * ∑ i, fderiv ℝ (realFlux d K u i) x (d i)) =
      ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        v x * ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x (d i) (d j) := by
    apply setIntegral_congr_fun hS
    intro x hx
    rcases hdiv x hx with hd | hz
    · exact congrArg (fun t : ℝ => v x * t) (realFlux_divergence_at d K hK hu x hd)
    · simp only [hz.eq_of_nhds, zero_mul]
  rw [hvEq, huEq] at he
  exact he

end OAI.Analysis.PDE.Green
