import OAI.Analysis.PDE.Concentration.WeightedLattice
import OAI.Analysis.PDE.Green.Localized.SmallGreen

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.PDE.Green
open scoped Topology

theorem real_operator_second_green_lattice_localized_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x ∈ (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      (∀ j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in Icc a b,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))) k *
        ‖v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))‖) ≤ W)
    (hboundary : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖OAI.Analysis.PDE.Green.normalRealFlux (fun i => EuclideanSpace.single i 1) K r u y‖ ≤ ε) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hface : CompatibleLatticeFaces c L a b r
      (OAI.Analysis.PDE.Green.secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    ‖(∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) -
    ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))‖ ≤ |L.toLinearEquiv.toLinearMap.det| * (ε * W) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hq₀ : ContDiff ℝ 1 (fun x => -OAI.Analysis.PDE.Green.normalRealFlux d K r u x) :=
    (OAI.Analysis.PDE.Green.contDiff_normalRealFlux d K hK hr hu).neg
  have hq₁ : ContDiff ℝ 1 (fun x => u x * OAI.Analysis.PDE.Green.normalRealFlux d K r v x) :=
    (hu.of_le (by norm_num)).mul (OAI.Analysis.PDE.Green.contDiff_normalRealFlux d K hK hr hv)
  have hloc : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧
        (∀ᶠ y in 𝓝 x, r y = 0 → ‖-OAI.Analysis.PDE.Green.normalRealFlux d K r u y‖ ≤ ε) ∧
        (∀ᶠ y in 𝓝 x, r y = 0 → u y * OAI.Analysis.PDE.Green.normalRealFlux d K r v y = 0)) ∨
      (v =ᶠ[𝓝 x] (fun _ => 0)) ∧
      ((fun y => u y * OAI.Analysis.PDE.Green.normalRealFlux d K r v y) =ᶠ[𝓝 x] (fun _ => 0)) := by
    intro x hx hrx
    rcases hboundary x hx hrx with ⟨hreg, hlocal⟩ | hz
    · refine Or.inl ⟨hreg, ?_, ?_⟩
      · filter_upwards [hlocal] with y hy hyr
        simpa only [norm_neg] using (hy hyr).2
      · filter_upwards [hlocal] with y hy hyr
        simp only [(hy hyr).1, zero_mul]
    · refine Or.inr ⟨hz, ?_⟩
      filter_upwards [hz, OAI.Analysis.PDE.Green.secondGreenFlux_eventually_zero d K u v x hz] with y hyv hyF
      have hh := OAI.Analysis.PDE.Green.secondGreenFlux_normal_decomposition d K r u v y
      simp only [hyF, mul_zero, Finset.sum_const_zero, hyv, zero_mul, zero_add] at hh
      exact hh.symm
  have hcompact : IsCompact (euclideanLatticeCell c L a b) :=
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.image L.continuous)
  obtain ⟨C, hC, hbound⟩ := OAI.Analysis.PDE.Green.localized_product_boundary_bound hcompact
    (hr.of_le (by norm_num)) hq₀ hq₁ hv.continuous hε hloc
  have he := weighted_euclidean_lattice_divergence_bound c L a b hab
    (OAI.Analysis.PDE.Green.secondGreenFlux d K u v) (OAI.Analysis.PDE.Green.contDiff_secondGreenFlux d K hK hu hv)
    (hr.of_le (by norm_num)) hv.continuous hε hW
    (fun x hx => by
      rw [OAI.Analysis.PDE.Green.secondGreenFlux_normal_decomposition]
      exact hbound x hx) hface
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) ⊆ _)
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K v i) x (d i))
      ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hv i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K u i) x (d i))
      ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hu i) (d i))))
  change ‖∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.secondGreenFlux d K u v i) x (d i)‖ ≤ |L.toLinearEquiv.toLinearMap.det| * (ε * W) at he
  simp_rw [OAI.Analysis.PDE.Green.secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have hS : MeasurableSet ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) :=
    (measurableSet_euclideanLatticeCell c L a b).inter
      (isOpen_lt hr.continuous continuous_const).measurableSet
  have hvEq : (∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      u x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K v i) x (d i)) =
      ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
        u x * ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j) := by
    apply setIntegral_congr_fun hS
    intro x hx
    rcases hdiv x hx with hd | hz
    · exact congrArg (fun t : ℝ => u x * t) (OAI.Analysis.PDE.Green.realFlux_divergence_at d K hK hv x hd)
    · have hfirst : fderiv ℝ v x = 0 := by simpa using hz.fderiv_eq (𝕜 := ℝ)
      have hsecond : fderiv ℝ (fderiv ℝ v) x = 0 := by
        simpa using (hz.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
      simp [OAI.Analysis.PDE.Green.fderiv_realFlux d K hK hv, hfirst, hsecond]
  have huEq : (∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      v x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K u i) x (d i)) =
      ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
        v x * ∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x (d i) (d j) := by
    apply setIntegral_congr_fun hS
    intro x hx
    rcases hdiv x hx with hd | hz
    · exact congrArg (fun t : ℝ => v x * t) (OAI.Analysis.PDE.Green.realFlux_divergence_at d K hK hu x hd)
    · simp only [hz.eq_of_nhds, zero_mul]
  rw [hvEq, huEq] at he
  exact he

end OAI.Analysis.PDE.Concentration
