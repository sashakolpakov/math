import Mathlib

/-! # Strong Topology -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.StrongTopology

noncomputable section

/-! Strong operator topology for a group acting by isometries. This is
used to prove the topological-group realization clause of UnitarySplitting. -/

open Filter
open scoped _root_.Topology

theorem continuous_joint_isometries
    {A X : Type*} [TopologicalSpace A] [PseudoMetricSpace X]
    (f : A → X → X) (hf : ∀ a, Isometry (f a))
    (hc : ∀ x, Continuous (fun a => f a x)) :
    Continuous (fun p : A × X => f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨a, x⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hx : Tendsto (fun p : A × X => dist p.2 x) (𝓝 (a, x)) (𝓝 0) := by
    simpa only [dist_self] using
      ((continuous_snd.dist (continuous_const : Continuous (fun _ : A × X => x))).tendsto (a, x))
  have ha : Tendsto (fun p : A × X => dist (f p.1 x) (f a x)) (𝓝 (a, x)) (𝓝 0) := by
    simpa only [Function.comp_def, dist_self] using
      (((hc x).comp continuous_fst).dist
        (continuous_const : Continuous (fun _ : A × X => f a x))).tendsto (a, x)
  apply squeeze_zero (fun _ => dist_nonneg) (fun p => ?_)
    (by simpa only [add_zero] using hx.add ha)
  simpa only [(hf p.1).dist_eq] using dist_triangle (f p.1 p.2) (f p.1 x) (f a x)

variable {G A S : Type*} [Group G] [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [NormedAddCommGroup S] [NormedSpace ℂ S]

def observations (p : G →* A) (r : G →* (S ≃ₗ[ℂ] S)) (g : G) :
    A × ((S × S) → ℝ) × ((S × S) → ℝ) :=
  (p g, fun q => dist (r g q.1) q.2, fun q => dist (r g⁻¹ q.1) q.2)

abbrev operatorTopology (p : G →* A) (r : G →* (S ≃ₗ[ℂ] S)) : TopologicalSpace G :=
  TopologicalSpace.induced (observations p r) inferInstance

theorem operator_isTopologicalGroup (p : G →* A) (r : G →* (S ≃ₗ[ℂ] S))
    (hr : ∀ g, Isometry (r g)) :
    letI : TopologicalSpace G := operatorTopology p r
    IsTopologicalGroup G := by
  let : TopologicalSpace G := operatorTopology p r
  have ho : Continuous (observations p r) := continuous_induced_dom
  have hp : Continuous p := continuous_fst.comp ho
  have hfDist (x y : S) : Continuous (fun g : G => dist (r g x) y) :=
    (continuous_apply (x, y)).comp (continuous_fst.comp (continuous_snd.comp ho))
  have hiDist (x y : S) : Continuous (fun g : G => dist (r g⁻¹ x) y) :=
    (continuous_apply (x, y)).comp (continuous_snd.comp (continuous_snd.comp ho))
  have hf (x : S) : Continuous (fun g : G => r g x) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_self] using (hfDist x (r g x)).tendsto g
  have hi (x : S) : Continuous (fun g : G => r g⁻¹ x) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_self] using (hiDist x (r g⁻¹ x)).tendsto g
  have hj := continuous_joint_isometries (fun g x => r g x) hr hf
  have hji := continuous_joint_isometries (fun g x => r g⁻¹ x) (fun g => hr g⁻¹) hi
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · change Continuous (fun q : G × G => p (q.1 * q.2))
      simp_rw [map_mul]
      exact (hp.comp continuous_fst).mul (hp.comp continuous_snd)
    · apply Continuous.prodMk
      · apply continuous_pi
        rintro ⟨x, y⟩
        change Continuous (fun q : G × G => dist (r (q.1 * q.2) x) y)
        simp only [map_mul, LinearEquiv.mul_apply]
        exact (hj.comp (continuous_fst.prodMk ((hf x).comp continuous_snd))).dist continuous_const
      · apply continuous_pi
        rintro ⟨x, y⟩
        change Continuous (fun q : G × G => dist (r (q.1 * q.2)⁻¹ x) y)
        simp only [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
        exact (hji.comp (continuous_snd.prodMk ((hi x).comp continuous_fst))).dist continuous_const
  · apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · change Continuous (fun g : G => p g⁻¹)
      simp_rw [map_inv]
      exact continuous_inv.comp hp
    · apply Continuous.prodMk
      · apply continuous_pi
        rintro ⟨x, y⟩
        exact (hi x).dist continuous_const
      · apply continuous_pi
        rintro ⟨x, y⟩
        change Continuous (fun g : G => dist (r g⁻¹⁻¹ x) y)
        simpa only [inv_inv] using (hf x).dist continuous_const

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.StrongTopology
