import OAI.RepresentationTheory.Theta.Geometric.Universal.DimensionBound
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties
import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness

/-! # Component Dimension Bound -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original smooth projective PEL components have complex
dimension at most two; no component dimension is assumed. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.component_dimension_le_two (hg : D.pel.HasIntegralModelGeometry)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (j : Fin D.pel.componentCount) :
    (D.componentVariety hg j).complexDimension ≤ 2 := by
  let : IsIntegral (D.componentComplex j).left := D.component_integral hg j
  let : Smooth (D.componentComplex j).hom := (D.component_smooth_proper_connected hg j).1
  let X := D.componentVariety hg j
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let f : X.toOver ⟶ D.pel.complexSpace := D.componentComplexInclusion j
  let : IsOpenImmersion f.left := D.componentComplexInclusion_open hg j
  let : Mono f := Over.mono_of_mono_left f
  let x : X.analyticSpace := Classical.choice X.analyticSpace_nonempty
  exact Universal.DimensionBound.complexUniversal_dimension_le_two D.pel hg f x hs hdegree

end

end OAI.RepresentationTheory.Theta.Geometric
