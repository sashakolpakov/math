import OAI.Analysis.PDE.Concentration.Physical.Flux
import OAI.Analysis.PDE.Concentration.Physical.Extension
import OAI.Analysis.PDE.Dirichlet.Boundary.Normal
import OAI.Analysis.PDE.Green.Physical.Propagation

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem contDiffAt_physicalFullDefining (d : ℕ) (a : ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : physicalNullHeight d x ≠ 0) :
    ContDiffAt ℝ ∞ (OAI.Analysis.PDE.Green.physicalFullDefining d a) x := by
  have hc : ContDiff ℝ ∞ (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 =>
      (physicalToNullCurrentPoint d x).2) := by
    unfold physicalToNullCurrentPoint
    fun_prop
  rw [physicalFullDefining_eq_null]
  exact ((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a _ hx).of_le (by simp)).comp x hc.contDiffAt

theorem physicalFullDefining_fderiv_ne_zero (d : ℕ) (a : ℝ) (ha : 0 < a)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (ht' : ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ≤ 4)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0) :
    fderiv ℝ (OAI.Analysis.PDE.Green.physicalFullDefining d a) x ≠ 0 := by
  let p := OAI.Analysis.PDE.Green.fullPhysicalProjection d x
  let f : ℂ × (Option (Fin d) → ℂ) → ℝ := fun q =>
    OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a q.1 q.2
  have hp : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2 = 0 := hr
  have hy := (OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a (OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2) ha
    (by simpa only [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] using ht) (hp.le.trans (by norm_num))).1
  have hY : OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2 none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  have he : ContDiff ℝ ∞ (fun q : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalEmbedding q.1 q.2) := by
    have ht : ContDiff ℝ ∞ (OAI.Analysis.Calculus.Current.physicalTimeOffset (d := d)) := by
      apply contDiff_pi.mpr
      intro i
      cases i with
      | none => simpa only [OAI.Analysis.Calculus.Current.physicalTimeOffset, id_eq] using contDiff_id.const_smul ((Real.sqrt 2)⁻¹)
      | some i => cases i with
        | none => simpa only [OAI.Analysis.Calculus.Current.physicalTimeOffset, id_eq] using contDiff_id.const_smul (-(Real.sqrt 2)⁻¹)
        | some i => exact contDiff_const
    exact ((OAI.Analysis.Calculus.Current.physicalLift d).contDiff.comp contDiff_snd).add (ht.comp contDiff_fst)
  have hf : DifferentiableAt ℝ f p :=
    (((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a _ hY).of_le (by simp)).comp p he.contDiffAt).differentiableAt (by simp)
  have hn : fderiv ℝ f p ≠ 0 := by
    intro hz
    have hs : fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1) p.2 = 0 := by
      have hd := (hf.hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
      change fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ _)) at hd
      rw [hz, ContinuousLinearMap.zero_comp] at hd
      exact hd
    have hl := OAI.Analysis.Calculus.Current.physicalFiberDefining_fderiv_norm_lower a p.1 p.2 ha ht ht' hp.le
      (by rw [hp]; norm_num)
    rw [hs, norm_zero] at hl
    norm_num at hl
  exact OAI.Analysis.PDE.Green.fderiv_comp_surjective_ne_zero (OAI.Analysis.PDE.Green.fullPhysicalProjection d)
    (OAI.Analysis.PDE.Green.fullPhysicalProjection_surjective d) hf hn

theorem physicalFullDefining_gradient_norm_le (d : ℕ) (a : ℝ) (ha : 0 < a)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
    ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x‖ ≤
      40 * ((d : ℝ) + 1) ^ 2 / a := by
  have hy := physicalNullHeight_on_closed_fiber d a ha x ht hr
  have hY : physicalNullHeight d x ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  rw [physicalFullDefining_gradient d a x hY]
  have hr' : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a (physicalToNullCurrentPoint d x).2 ≤ 0 := by
    rwa [physicalFullDefining_eq_null] at hr
  exact (norm_physicalVector_le _).trans
    ((mul_le_mul_of_nonneg_left (OAI.Analysis.Calculus.Current.fiberGradient_norm_le a ha _ hy hr') (by norm_num)).trans_eq (by ring))

theorem quaternionGradient_factor_of_fderiv {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {u r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s} {b : ℝ}
    (hb : fderiv ℝ u x = b • fderiv ℝ r x) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x = b • OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x := by
  have he : OAI.Analysis.PDE.Dirichlet.realGradient u x = b • OAI.Analysis.PDE.Dirichlet.realGradient r x := by
    funext i
    simp only [OAI.Analysis.PDE.Dirichlet.realGradient, hb, smul_apply, Pi.smul_apply]
  funext i
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionGradient, he, OAI.Analysis.Calculus.Quaternion.gradientMap, Pi.smul_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

/-- Quantitative full (including time) boundary gradient from a uniform
fiber barrier. No global higher-regularity estimate is used. -/
theorem physical_boundary_gradient_of_barrier {d : ℕ} {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : Differentiable ℝ u)
    (hbar : ∀ y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, B * OAI.Analysis.PDE.Green.physicalFullDefining d a y ≤ u y ∧ u y ≤ 0)
    (hzero : ∀ y, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a y = 0 → u y = 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (ht : a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0) :
    ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots u x‖ ≤ B * (40 * ((d : ℝ) + 1) ^ 2 / a) := by
  have hy := physicalNullHeight_on_closed_fiber d a ha x ht.1.le hr.le
  have hY : physicalNullHeight d x ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  have hc : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 => ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖) :=
    (continuous_fst.comp (OAI.Analysis.PDE.Green.fullPhysicalProjection d).continuous).norm
  have hn : ∀ᶠ y in 𝓝 x, OAI.Analysis.PDE.Green.physicalFullDefining d a y < 0 → y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a := by
    filter_upwards [hc.continuousAt.eventually (Ioo_mem_nhds ht.1 ht.2)] with y hy
    exact fun hyr => ⟨hy, hyr⟩
  obtain ⟨b, hb0, hbB, hfactor⟩ := OAI.Analysis.PDE.Dirichlet.boundary_gradient_factor_of_barriers (hu x)
    ((contDiffAt_physicalFullDefining d a x hY).differentiableAt (by simp))
    (hzero x ht hr) hr (physicalFullDefining_fderiv_ne_zero d a ha x ht.1.le ht.2.le hr)
    (le_refl (0 : ℝ)) hB (fun y hy => by simpa only [zero_mul] using hbar y hy) hn
  rw [quaternionGradient_factor_of_fderiv OAI.Analysis.Calculus.Quaternion.threeSlots hfactor, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hb0]
  exact mul_le_mul hbB (physicalFullDefining_gradient_norm_le d a ha x ht.1.le hr.le)
    (norm_nonneg _) hB

theorem physical_boundary_gradient_of_local_barrier {d : ℕ} {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0 → DifferentiableAt ℝ u x)
    (hbar : ∀ y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, B * OAI.Analysis.PDE.Green.physicalFullDefining d a y ≤ u y ∧ u y ≤ 0)
    (hzero : ∀ y, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a y = 0 → u y = 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (ht : a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0) :
    ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots u x‖ ≤ B * (40 * ((d : ℝ) + 1) ^ 2 / a) := by
  have hy := physicalNullHeight_on_closed_fiber d a ha x ht.1.le hr.le
  have hY : physicalNullHeight d x ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  have hc : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 => ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d y).1‖) :=
    (continuous_fst.comp (OAI.Analysis.PDE.Green.fullPhysicalProjection d).continuous).norm
  have hn : ∀ᶠ y in 𝓝 x, OAI.Analysis.PDE.Green.physicalFullDefining d a y < 0 → y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a := by
    filter_upwards [hc.continuousAt.eventually (Ioo_mem_nhds ht.1 ht.2)] with y hy
    exact fun hyr => ⟨hy, hyr⟩
  obtain ⟨b, hb0, hbB, hfactor⟩ := OAI.Analysis.PDE.Dirichlet.boundary_gradient_factor_of_barriers (hu x ht hr.le)
    ((contDiffAt_physicalFullDefining d a x hY).differentiableAt (by simp))
    (hzero x ht hr) hr (physicalFullDefining_fderiv_ne_zero d a ha x ht.1.le ht.2.le hr)
    (le_refl (0 : ℝ)) hB (fun y hy => by simpa only [zero_mul] using hbar y hy) hn
  rw [quaternionGradient_factor_of_fderiv OAI.Analysis.Calculus.Quaternion.threeSlots hfactor, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hb0]
  exact mul_le_mul hbB (physicalFullDefining_gradient_norm_le d a ha x ht.1.le hr.le)
    (norm_nonneg _) hB


end OAI.Analysis.PDE.Concentration
