import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Frames
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight

/-! # Form Partition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition

noncomputable section

section

/-! Finite reconstruction of actual bundle forms by supported frame coordinates. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CompactSpace M] [T2Space M] (u : Connecting.holomorphicUnitCohomology E M)

def holomorphicLineComplexPartition (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) (x : M) : ℂ :=
  HolomorphicLine.MetricWeight.holomorphicLineSmoothPartition u i x

theorem holomorphicLineComplexPartition_smooth (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (holomorphicLineComplexPartition u i) :=
  Complex.ofRealCLM.contDiff.contMDiff.comp (HolomorphicLine.MetricWeight.holomorphicLineSmoothPartition u i).contMDiff

theorem holomorphicLineComplexPartition_support (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    tsupport (holomorphicLineComplexPartition u i) ⊆ CohomologyTransitions.holomorphicCohomologyDomain E M u i.val := by
  have h : Function.support (holomorphicLineComplexPartition u i) =
      Function.support (HolomorphicLine.MetricWeight.holomorphicLineSmoothPartition u i) := by
    ext x
    simp only [Function.mem_support, holomorphicLineComplexPartition, ne_eq, Complex.ofReal_eq_zero]
  change closure (Function.support (holomorphicLineComplexPartition u i)) ⊆ _
  rw [h]
  exact HolomorphicLine.MetricWeight.holomorphicLineSmoothPartition_support u i

theorem holomorphicLineComplexPartition_sum (x : M) :
    ∑ i, holomorphicLineComplexPartition u i x = 1 := by
  simp only [holomorphicLineComplexPartition, ← Complex.ofReal_sum, HolomorphicLine.MetricWeight.holomorphicLineSmoothPartition_sum,
    Complex.ofReal_one]

variable (n : ℕ)

def holomorphicLineSmoothFormCoordinate (j : M)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u j)) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] (TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin n]→L[ℝ] ℂ) where
  toFun s := s.val j x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def holomorphicLineFrameLocalization (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  (SupportedForms.holomorphicLineSupportedExtension u (CohomologyTransitions.holomorphicCohomologyDomain E M u i.val) n
    (holomorphicLineComplexPartition u i) (holomorphicLineComplexPartition_smooth u i)
    (holomorphicLineComplexPartition_support u i)).comp (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top)

theorem holomorphicLineFrameLocalization_eq_mul (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicLineFrameLocalization u n i s = SupportedForms.holomorphicLineSmoothMul u ⊤ n
      (holomorphicLineComplexPartition u i) (holomorphicLineComplexPartition_smooth u i) s :=
  SupportedForms.holomorphicLineSupportedExtension_of_global u _ n _ _ _ s

theorem holomorphicLineFrameLocalization_sum (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ∑ i, holomorphicLineFrameLocalization u n i s = s := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  change holomorphicLineSmoothFormCoordinate u n j x (∑ i, holomorphicLineFrameLocalization u n i s) = _
  rw [map_sum]
  simp only [holomorphicLineSmoothFormCoordinate, LinearMap.coe_mk, AddHom.coe_mk,
    holomorphicLineFrameLocalization_eq_mul, SupportedForms.holomorphicLineSmoothMul_apply]
  rw [← Finset.sum_smul, holomorphicLineComplexPartition_sum, one_smul]

def holomorphicLineFrameCutoffExtension (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (CohomologyTransitions.holomorphicCohomologyDomain E M u i.val) n →ₗ[ℂ]
      HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  (SupportedForms.holomorphicLineSupportedExtension u (CohomologyTransitions.holomorphicCohomologyDomain E M u i.val) n
    (holomorphicLineComplexPartition u i) (holomorphicLineComplexPartition_smooth u i)
    (holomorphicLineComplexPartition_support u i)).comp
      (HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i.val le_rfl n).symm.toLinearMap

theorem holomorphicLineFrameCutoffExtension_reconstruct (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ∑ i, holomorphicLineFrameCutoffExtension u n i
      (HolomorphicSmooth.Frames.holomorphicLineSmoothFrameValue u i.val le_rfl n (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top s)) = s := by
  have h (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) : holomorphicLineFrameCutoffExtension u n i
      (HolomorphicSmooth.Frames.holomorphicLineSmoothFrameValue u i.val le_rfl n (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top s)) =
        holomorphicLineFrameLocalization u n i s := by
    change SupportedForms.holomorphicLineSupportedExtension u _ n _ _ _
      (HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame u i.val le_rfl n
        (HolomorphicSmooth.Frames.holomorphicLineSmoothFrameValue u i.val le_rfl n (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top s))) = _
    rw [HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame_frameValue]
    rfl
  simp_rw [h]
  exact holomorphicLineFrameLocalization_sum u n s

end

/-! Actual smooth cutoffs equal to one near each original partition support,
with topological support still inside the corresponding holomorphic frame. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem exists_smoothComplexCutoff_near_closed (U : Opens M) (K : Set M)
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M)) :
    ∃ f : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f ∧ tsupport f ⊆ (U : Set M) ∧
      (∀ᶠ x in 𝓝ˢ K, f x = 1) := by
  have hd : Disjoint (U : Set M)ᶜ K := disjoint_left.mpr fun x hx h => hx (hKU h)
  obtain ⟨f, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, E) U.isOpen.isClosed_compl hK hd (n := ⊤)
  refine ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp f.contMDiff, ?_, ?_⟩
  · intro x hx
    by_contra hxU
    have hz : (fun y => (f y : ℂ)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hxU)] with y hy
      simp only [hy, Complex.ofReal_zero, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  · filter_upwards [hone] with x hx
    simp only [hx, Complex.ofReal_one]

variable (u : Connecting.holomorphicUnitCohomology E M) (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)

theorem exists_holomorphicLineFrameCutoff :
    ∃ f : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f ∧
      tsupport f ⊆ CohomologyTransitions.holomorphicCohomologyDomain E M u i.val ∧
      (∀ᶠ x in 𝓝ˢ (tsupport (holomorphicLineComplexPartition u i)), f x = 1) :=
  exists_smoothComplexCutoff_near_closed (CohomologyTransitions.holomorphicCohomologyDomain E M u i.val)
    (tsupport (holomorphicLineComplexPartition u i)) (isClosed_tsupport _)
    (holomorphicLineComplexPartition_support u i)

def holomorphicLineFrameCutoff : M → ℂ := (exists_holomorphicLineFrameCutoff u i).choose

theorem holomorphicLineFrameCutoff_smooth :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (holomorphicLineFrameCutoff u i) :=
  (exists_holomorphicLineFrameCutoff u i).choose_spec.1

theorem holomorphicLineFrameCutoff_support :
    tsupport (holomorphicLineFrameCutoff u i) ⊆ CohomologyTransitions.holomorphicCohomologyDomain E M u i.val :=
  (exists_holomorphicLineFrameCutoff u i).choose_spec.2.1

theorem holomorphicLineFrameCutoff_one_near :
    ∀ᶠ x in 𝓝ˢ (tsupport (holomorphicLineComplexPartition u i)), holomorphicLineFrameCutoff u i x = 1 :=
  (exists_holomorphicLineFrameCutoff u i).choose_spec.2.2

theorem holomorphicLineFrameCutoff_one (x : M) (hx : x ∈ tsupport (holomorphicLineComplexPartition u i)) :
    holomorphicLineFrameCutoff u i x = 1 :=
  (holomorphicLineFrameCutoff_one_near u i).self_of_nhdsSet x hx

theorem holomorphicLineFrameCutoff_mul_partition (x : M) :
    holomorphicLineFrameCutoff u i x * holomorphicLineComplexPartition u i x =
      holomorphicLineComplexPartition u i x := by
  by_cases hx : x ∈ tsupport (holomorphicLineComplexPartition u i)
  · rw [holomorphicLineFrameCutoff_one u i x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
