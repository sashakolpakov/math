import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Bundle

/-! # Data -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data

noncomputable section

section

/-! Actual holomorphic section coordinates of the constructed line bundle. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

abbrev holomorphicLineLocalSections (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :=
  ∀ i : M, Holomorphic.Exponential.HolomorphicFunction (E := E) (M := ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i))

def holomorphicLineSectionSubmodule (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    Submodule ℂ (holomorphicLineLocalSections u U) where
  carrier := {s | ∀ (i j x : M) (hx : x ∈ U)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j),
      s j ⟨x, hx, hj⟩ = (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ * s i ⟨x, hx, hi⟩}
  zero_mem' := by
    intro i j x hx hi hj
    exact (mul_zero _).symm
  add_mem' := by
    intro s t hs ht i j x hx hi hj
    change s j ⟨x, hx, hj⟩ + t j ⟨x, hx, hj⟩ = _ * (s i ⟨x, hx, hi⟩ + t i ⟨x, hx, hi⟩)
    rw [hs i j x hx hi hj, ht i j x hx hi hj, mul_add]
  smul_mem' := by
    intro z s hs i j x hx hi hj
    change z * s j ⟨x, hx, hj⟩ = _ * (z * s i ⟨x, hx, hi⟩)
    rw [hs i j x hx hi hj]
    ring

abbrev HolomorphicLineSection (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :=
  holomorphicLineSectionSubmodule u U

instance holomorphicLineSection_addCommGroup (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    AddCommGroup (HolomorphicLineSection u U) := Module.addCommMonoidToAddCommGroup ℂ

@[ext]
theorem holomorphicLineSection_ext {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U : Opens M}
    {s t : HolomorphicLineSection u U}
    (h : ∀ (i : M) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)), s.val i x = t.val i x) : s = t := by
  apply Subtype.ext
  funext i
  exact ContMDiffMap.ext (h i)

def holomorphicLineSectionRestrict {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V : Opens M} (h : V ≤ U) :
    HolomorphicLineSection u U →ₗ[ℂ] HolomorphicLineSection u V where
  toFun s := ⟨fun i => (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map
    (homOfLE (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) h)).op (s.val i), by
      intro i j x hx hi hj
      exact s.property i j x (h hx) hi hj⟩
  map_add' s t := by
    apply holomorphicLineSection_ext
    intro i x
    rfl
  map_smul' z s := by
    apply holomorphicLineSection_ext
    intro i x
    rfl

theorem holomorphicLineSectionRestrict_self {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U : Opens M}
    (s : HolomorphicLineSection u U) : holomorphicLineSectionRestrict le_rfl s = s := by
  apply holomorphicLineSection_ext
  intro i x
  rfl

theorem holomorphicLineSectionRestrict_comp {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V W : Opens M}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : HolomorphicLineSection u U) :
    holomorphicLineSectionRestrict hWV (holomorphicLineSectionRestrict hVU s) =
      holomorphicLineSectionRestrict (hWV.trans hVU) s := by
  apply holomorphicLineSection_ext
  intro i x
  rfl

end

/-! Genuine holomorphic frame isomorphisms for the constructed line-bundle section coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicOpenRestriction {U V : Opens M} (h : V ≤ U) :
    Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) →+* Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V) :=
  ((Holomorphic.Sheaves.holomorphicRingSheaf E M).obj.map (homOfLE h).op).hom

variable (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {U : Opens M} (i : M)
  (hU : U ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)

def holomorphicLineSectionOfFrame (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) : HolomorphicLineSection u U :=
  ⟨fun j => holomorphicOpenRestriction (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) hU)
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val * holomorphicOpenRestriction inf_le_left f, by
    intro j k x hx hj hk
    change (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i k).val ⟨x, hU hx, hk⟩ * f ⟨x, hx⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u j k).val ⟨x, hj, hk⟩ *
        ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hU hx, hj⟩ * f ⟨x, hx⟩)
    rw [← Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M u i j k x (hU hx) hj hk]
    ring⟩

def holomorphicLineSectionFrameValue (s : HolomorphicLineSection u U) : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) :=
  holomorphicOpenRestriction (le_inf le_rfl hU) (s.val i)

theorem holomorphicLineSectionFrameValue_ofFrame (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    holomorphicLineSectionFrameValue u i hU (holomorphicLineSectionOfFrame u i hU f) = f := by
  apply ContMDiffMap.ext
  intro x
  change (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i i).val ⟨x.val, hU x.property, hU x.property⟩ * f x = f x
  rw [Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self E M u i x.val (hU x.property), one_mul]

theorem holomorphicLineSectionOfFrame_frameValue (s : HolomorphicLineSection u U) :
    holomorphicLineSectionOfFrame u i hU (holomorphicLineSectionFrameValue u i hU s) = s := by
  apply holomorphicLineSection_ext
  intro j x
  exact (s.property i j x.val x.property.1 (hU x.property.1) x.property.2).symm

def holomorphicLineSectionFrameEquiv :
    HolomorphicLineSection u U ≃ₗ[ℂ] Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) where
  toFun := holomorphicLineSectionFrameValue u i hU
  invFun := holomorphicLineSectionOfFrame u i hU
  left_inv := holomorphicLineSectionOfFrame_frameValue u i hU
  right_inv := holomorphicLineSectionFrameValue_ofFrame u i hU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
