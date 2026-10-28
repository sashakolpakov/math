import OAI.RepresentationTheory.Theta.Geometric.Period.ChartDifferences
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.CompactOpen

/-! # Automorphy Bundle Metric -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! A continuous lattice factor constructs an actual complex line bundle
on the period torus, using its local period lifts. -/

open _root_.Topology

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

structure Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor where
  value : Φ.periodIntegerLattice → Φ.space → ℂ
  zero : ∀ z, value 0 z = 1
  add : ∀ l m z, value (l + m) z = value l (z + m.val) * value m z
  continuous : ∀ l, Continuous (value l)

variable {Φ} (J : Φ.AutomorphyFactor)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.continuous_joint : Continuous (fun p : Φ.periodIntegerLattice × Φ.space => J.value p.1 p.2) := by
  let f : C(Φ.periodIntegerLattice, C(Φ.space, ℂ)) :=
    ⟨fun l => ⟨J.value l, J.continuous l⟩, continuous_of_discreteTopology⟩
  exact ContinuousMap.continuous_uncurry_of_continuous f

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor (i j z : Φ.periodTorus) : ℂ :=
  J.value (Φ.periodChartDifference i j z) (Φ.periodChart i z)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor_self (i z : Φ.periodTorus) : J.transitionFactor i i z = 1 := by
  simp only [Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor, Φ.periodChartDifference_self, J.zero]

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor_comp (i j k z : Φ.periodTorus)
    (h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source ∩ (Φ.periodChart k).source) :
    J.transitionFactor j k z * J.transitionFactor i j z = J.transitionFactor i k z := by
  have hshift : Φ.periodChart i z + (Φ.periodChartDifference i j z).val = Φ.periodChart j z := by
    rw [Φ.periodChartDifference_val i j z h.1]
    abel
  have hc := J.add (Φ.periodChartDifference j k z) (Φ.periodChartDifference i j z) (Φ.periodChart i z)
  rw [Φ.periodChartDifference_add i j k z h, hshift] at hc
  exact hc.symm

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor_continuousOn (i j : Φ.periodTorus) :
    ContinuousOn (J.transitionFactor i j) ((Φ.periodChart i).source ∩ (Φ.periodChart j).source) :=
  J.continuous_joint.comp_continuousOn ((Φ.periodChartDifference_continuousOn i j).prodMk
    ((Φ.periodChart i).continuousOn.mono Set.inter_subset_left))

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.vectorBundleCore : VectorBundleCore ℂ Φ.periodTorus ℂ Φ.periodTorus where
  baseSet i := (Φ.periodChart i).source
  isOpen_baseSet i := (Φ.periodChart i).open_source
  indexAt := id
  mem_baseSet_at := Φ.mem_periodChart_source
  coordChange i j z := J.transitionFactor i j z • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i z _ v := by
    simp only [J.transitionFactor_self, one_smul, ContinuousLinearMap.id_apply]
  continuousOn_coordChange i j := (J.transitionFactor_continuousOn i j).smul continuousOn_const
  coordChange_comp i j k z hz v := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      ← mul_assoc, J.transitionFactor_comp i j k z hz]

end

/-! A compatible positive weight descends to a positive continuous
squared norm on the actual glued line bundle. -/

open _root_.Topology Filter

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)
  (W : Φ.space → ℝ)

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.bundleNormSq (p : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber) : ℝ :=
  W (Φ.periodChart p.proj p.proj) * Complex.normSq p.snd

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.bundleNormSq_nonneg (hW : ∀ z, 0 < W z) (p : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber) :
    0 ≤ J.bundleNormSq W p := mul_nonneg (hW _).le (Complex.normSq_nonneg _)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.bundleNormSq_eq_zero_iff (hW : ∀ z, 0 < W z) (p : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber) :
    J.bundleNormSq W p = 0 ↔ p.snd = 0 := by
  change W _ * Complex.normSq p.snd = 0 ↔ _
  rw [mul_eq_zero]
  simp only [(hW _).ne', false_or]
  exact Complex.normSq_eq_zero

variable (htrans : ∀ l z, ‖J.value l z‖ ^ 2 * W (z + l.val) = W z)

include htrans in
theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.transitionFactor_metric (i j z : Φ.periodTorus)
    (h : z ∈ (Φ.periodChart i).source ∩ (Φ.periodChart j).source) :
    W (Φ.periodChart j z) * ‖J.transitionFactor i j z‖ ^ 2 = W (Φ.periodChart i z) := by
  have hshift : Φ.periodChart i z + (Φ.periodChartDifference i j z).val = Φ.periodChart j z := by
    rw [Φ.periodChartDifference_val i j z h]
    abel
  have ht := htrans (Φ.periodChartDifference i j z) (Φ.periodChart i z)
  rw [hshift, mul_comm] at ht
  exact ht

include htrans in
theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.bundleNormSq_local (i : Φ.periodTorus) (p : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber)
    (hp : p.proj ∈ (Φ.periodChart i).source) :
    J.bundleNormSq W p = W (Φ.periodChart i p.proj) * Complex.normSq (J.vectorBundleCore.localTriv i p).2 := by
  let t : ℂ := p.snd
  change W (Φ.periodChart p.proj p.proj) * Complex.normSq t =
    W (Φ.periodChart i p.proj) * Complex.normSq (J.transitionFactor p.proj i p.proj * t)
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (J.transitionFactor p.proj i p.proj), ← mul_assoc,
    J.transitionFactor_metric W htrans p.proj i p.proj ⟨Φ.mem_periodChart_source p.proj, hp⟩]

include htrans in
theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.bundleNormSq_continuous (hW : Continuous W) : Continuous (J.bundleNormSq W) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i : Φ.periodTorus := p.proj
  have hi : p.proj ∈ (Φ.periodChart i).source := Φ.mem_periodChart_source p.proj
  have hp : p ∈ (J.vectorBundleCore.localTriv i).source := hi
  have hb : ContinuousAt (fun r : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber => r.proj) p :=
    (FiberBundle.continuous_proj ℂ J.vectorBundleCore.Fiber).continuousAt
  have hc : ContinuousAt (Φ.periodChart i) p.proj :=
    ((Φ.periodChart i).continuousOn p.proj hi).continuousAt ((Φ.periodChart i).open_source.mem_nhds hi)
  have ht : ContinuousAt
      (fun r : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber => (J.vectorBundleCore.localTriv i r).2) p :=
    ((J.vectorBundleCore.localTriv i).continuousAt hp).snd
  have hs : ContinuousAt (fun r : Bundle.TotalSpace ℂ J.vectorBundleCore.Fiber =>
      W (Φ.periodChart i r.proj) * Complex.normSq (J.vectorBundleCore.localTriv i r).2) p :=
    (hW.continuousAt.comp (hc.comp hb)).mul (Complex.continuous_normSq.continuousAt.comp ht)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hb.eventually_mem ((Φ.periodChart i).open_source.mem_nhds hi)] with r hr
  exact J.bundleNormSq_local W htrans i r hr

end

end OAI.RepresentationTheory.Theta.Geometric
