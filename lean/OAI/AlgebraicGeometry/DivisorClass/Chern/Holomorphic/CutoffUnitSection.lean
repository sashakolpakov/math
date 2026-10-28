import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

/-! # Cutoff Unit Section -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffUnitSection

noncomputable section

/-! A genuine global smooth line section obtained by cutting off the unit in an original holomorphic frame. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))

def holomorphicLineCutoffUnitSection : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 :=
  HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i 0 f hf hs
    (GlobalRealScalarForm.globalRealScalarForm (fun _ : V.analyticSpace => (1 : ℝ)) contMDiff_const)

theorem holomorphicLineCutoffUnitSection_apply (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, V.analyticModel) x.val) :
    (holomorphicLineCutoffUnitSection V u i f hf hs).val j x v =
      f x * (CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val ⟨x.val, hx, x.property.2⟩ := by
  rw [holomorphicLineCutoffUnitSection, HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_apply u i 0 f hf hs _ j x hx]
  change f x * ((CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val _ *
    GlobalRealScalarForm.globalRealScalarForm (fun _ : V.analyticSpace => (1 : ℝ)) contMDiff_const x.val v) = _
  rw [GlobalRealScalarForm.globalRealScalarForm_apply, Complex.ofReal_one, mul_one]

theorem holomorphicLineCutoffUnitSection_restrict_one (U : Opens V.analyticSpace)
    (hU : U ≤ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (hfone : ∀ x ∈ U, f x = 1) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (holomorphicLineCutoffUnitSection V u i f hf hs) =
      HolomorphicLine.AntiForms.holomorphicLineSectionSmoothZeroForm u U (HolomorphicSection.Data.holomorphicLineSectionOfFrame u i hU 1) := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  ext v
  change (holomorphicLineCutoffUnitSection V u i f hf hs).val j ⟨x.val, trivial, x.property.2⟩ v =
    ManifoldZeroForms.holomorphicManifoldZeroForm ((HolomorphicSection.Data.holomorphicLineSectionOfFrame u i hU 1).val j) x v
  rw [holomorphicLineCutoffUnitSection_apply V u i f hf hs j _ (hU x.property.1) v,
    ManifoldZeroForms.holomorphicManifoldZeroForm_apply, hfone x.val x.property.1, one_mul]
  change _ = _ * (1 : ℂ)
  exact (mul_one _).symm

theorem holomorphicLineCutoffUnitSection_dbar_one (U : Opens V.analyticSpace)
    (hU : U ≤ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (hfone : ∀ x ∈ U, f x = 1) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤)
      (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ (holomorphicLineCutoffUnitSection V u i f hf hs)) = 0 := by
  rw [HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_restrict,
    holomorphicLineCutoffUnitSection_restrict_one V u i f hf hs U hU hfone]
  exact HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_of_holomorphic u U _

theorem holomorphicLineCutoffUnitSection_restrict_zero (U : Opens V.analyticSpace)
    (hU : ∀ x ∈ U, x ∉ tsupport f) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (holomorphicLineCutoffUnitSection V u i f hf hs) = 0 := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  exact HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_zero u i 0 f hf hs _ j
    ⟨x.val, trivial, x.property.2⟩ (hU x.val x.property.1)

theorem holomorphicLineCutoffUnitSection_dbar_zero (U : Opens V.analyticSpace)
    (hU : ∀ x ∈ U, x ∉ tsupport f) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤)
      (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ (holomorphicLineCutoffUnitSection V u i f hf hs)) = 0 := by
  rw [HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_restrict, holomorphicLineCutoffUnitSection_restrict_zero V u i f hf hs U hU, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffUnitSection
