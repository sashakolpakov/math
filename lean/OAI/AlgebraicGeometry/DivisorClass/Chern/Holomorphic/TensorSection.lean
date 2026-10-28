import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorGaugeTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

/-! # Tensor Section -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorSection

noncomputable section

section

/-! Original local holomorphic tensor sections use the actual sum-bundle gauges. -/

open _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u v : Connecting.holomorphicUnitCohomology E M)
  (s : HolomorphicSection.Data.HolomorphicLineSection u ⊤) (t : HolomorphicSection.Data.HolomorphicLineSection v ⊤) (i : M)

def holomorphicTensorSectionLocalValue : Exponential.HolomorphicFunction (E := E) (M := TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :=
  (TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val *
    HolomorphicSection.Data.holomorphicOpenRestriction (le_inf le_top (inf_le_right.trans inf_le_left)) (s.val i) *
    HolomorphicSection.Data.holomorphicOpenRestriction (le_inf le_top (inf_le_right.trans inf_le_right)) (t.val i)

def holomorphicTensorSectionLocal : HolomorphicSection.Data.HolomorphicLineSection (u + v) (TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :=
  HolomorphicSection.Data.holomorphicLineSectionOfFrame (u + v) i inf_le_left (holomorphicTensorSectionLocalValue u v s t i)

theorem holomorphicTensorSectionLocal_apply (j : M)
    (x : ↥(TensorGaugeTransitions.holomorphicTensorDomain E M u v i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M (u + v) j)) :
    (holomorphicTensorSectionLocal u v s t i).val j x =
      (CohomologyTransitions.holomorphicCohomologyTransition E M (u + v) i j).val ⟨x.val, x.property.1.1, x.property.2⟩ *
        ((TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val ⟨x.val, x.property.1⟩ *
          s.val i ⟨x.val, trivial, x.property.1.2.1⟩ * t.val i ⟨x.val, trivial, x.property.1.2.2⟩) := rfl

theorem holomorphicTensorSectionLocal_own_frame (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    (holomorphicTensorSectionLocal u v s t i).val i ⟨x.val, x.property, x.property.1⟩ =
      (TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val x *
        s.val i ⟨x.val, trivial, x.property.2.1⟩ * t.val i ⟨x.val, trivial, x.property.2.2⟩ := by
  rw [holomorphicTensorSectionLocal_apply,
    CohomologyTransitions.holomorphicCohomologyTransition_self E M (u + v) i x.val x.property.1, one_mul]

end

section

/-! The actual local tensor sections agree on every overlap by the original sum-bundle gauge and transition identities. -/

open _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem tensorSection_transition_product (p q r g h a b s t : ℂ)
    (hp : p * q = r) (hg : p * g = h * a * b) :
    r * (g * s * t) = q * (h * (a * s) * (b * t)) := by
  rw [← hp]
  calc
    _ = q * (p * g) * s * t := by ring
    _ = q * (h * a * b) * s * t := by rw [hg]
    _ = _ := by ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u v : Connecting.holomorphicUnitCohomology E M)
  (s : HolomorphicSection.Data.HolomorphicLineSection u ⊤) (t : HolomorphicSection.Data.HolomorphicLineSection v ⊤)

theorem holomorphicTensorSectionLocal_overlap (i j : M) :
    HolomorphicSection.Data.holomorphicLineSectionRestrict inf_le_left (holomorphicTensorSectionLocal u v s t i) =
      HolomorphicSection.Data.holomorphicLineSectionRestrict inf_le_right (holomorphicTensorSectionLocal u v s t j) := by
  apply HolomorphicSection.Data.holomorphicLineSection_ext
  intro k x
  change (holomorphicTensorSectionLocal u v s t i).val k ⟨x.val, x.property.1.1, x.property.2⟩ =
    (holomorphicTensorSectionLocal u v s t j).val k ⟨x.val, x.property.1.2, x.property.2⟩
  rw [holomorphicTensorSectionLocal_apply, holomorphicTensorSectionLocal_apply]
  have hsi := x.property.1.1
  have hsj := x.property.1.2
  rw [s.property i j x.val trivial hsi.2.1 hsj.2.1,
    t.property i j x.val trivial hsi.2.2 hsj.2.2]
  exact tensorSection_transition_product _ _ _ _ _ _ _ _ _
    (CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M (u + v) i j k x.val hsi.1 hsj.1 x.property.2)
    (TensorGaugeTransitions.holomorphicTensorGauge_transition E M u v i j x.val hsi hsj)

end

/-! Actual global holomorphic tensor sections, glued from the original gauges, with preservation of nonzero point values. -/

open _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u v : Connecting.holomorphicUnitCohomology E M)
  (s : HolomorphicSection.Data.HolomorphicLineSection u ⊤) (t : HolomorphicSection.Data.HolomorphicLineSection v ⊤)

theorem holomorphicTensorDomain_cover : (⊤ : Opens M) ≤ ⨆ i, TensorGaugeTransitions.holomorphicTensorDomain E M u v i := by
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, TensorGaugeTransitions.holomorphicTensorDomain_mem E M u v x⟩

theorem holomorphicTensorSectionGluing :
    ∃ g : HolomorphicSection.Data.HolomorphicLineSection (u + v) (⨆ i, TensorGaugeTransitions.holomorphicTensorDomain E M u v i),
      ∀ i, HolomorphicSection.Data.holomorphicLineSectionRestrict (le_iSup (TensorGaugeTransitions.holomorphicTensorDomain E M u v) i) g =
        holomorphicTensorSectionLocal u v s t i :=
  FunctionGluing.exists_holomorphicLineSection_glue (u + v) (TensorGaugeTransitions.holomorphicTensorDomain E M u v)
    (holomorphicTensorSectionLocal u v s t) (holomorphicTensorSectionLocal_overlap u v s t)

def holomorphicTensorSection : HolomorphicSection.Data.HolomorphicLineSection (u + v) ⊤ :=
  HolomorphicSection.Data.holomorphicLineSectionRestrict (holomorphicTensorDomain_cover u v)
    (holomorphicTensorSectionGluing u v s t).choose

theorem holomorphicTensorSection_apply (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    (holomorphicTensorSection u v s t).val i ⟨x.val, trivial, x.property.1⟩ =
      (TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val x *
        s.val i ⟨x.val, trivial, x.property.2.1⟩ * t.val i ⟨x.val, trivial, x.property.2.2⟩ := by
  have hg := congrArg (fun a : HolomorphicSection.Data.HolomorphicLineSection (u + v) (TensorGaugeTransitions.holomorphicTensorDomain E M u v i) =>
    a.val i ⟨x.val, x.property, x.property.1⟩) ((holomorphicTensorSectionGluing u v s t).choose_spec i)
  exact hg.trans (holomorphicTensorSectionLocal_own_frame u v s t i x)

theorem holomorphicTensorSection_nonzero (x : M)
    (hs : s.val x ⟨x, trivial, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩ ≠ 0)
    (ht : t.val x ⟨x, trivial, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M v).mem_domain x⟩ ≠ 0) :
    (holomorphicTensorSection u v s t).val x
      ⟨x, trivial, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M (u + v)).mem_domain x⟩ ≠ 0 := by
  have hv := holomorphicTensorSection_apply u v s t x ⟨x, TensorGaugeTransitions.holomorphicTensorDomain_mem E M u v x⟩
  exact hv ▸ mul_ne_zero (mul_ne_zero
    (SlitLog.holomorphicUnit_value_ne_zero (TensorGaugeTransitions.holomorphicTensorGauge E M u v x) _) hs) ht

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorSection
