import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

/-! # Component Maps -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.ComponentMaps

noncomputable section

/-! The open-immersion cycle maps agree with the existing maps on
integral components and recover the fundamental-cycle decomposition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

instance component_open (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    IsOpenImmersion (Component.Image.inclusion X C).left :=
  show IsOpenImmersion (X.componentInclusion C) from inferInstance

instance component_closed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    IsClosedImmersion (Component.Image.inclusion X C).left :=
  show IsClosedImmersion (X.componentInclusion C) from inferInstance

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

local instance component_dimension (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C

theorem supportImage_eq (C : irreducibleComponents X.carrier) (p : ℕ)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport p) :
    Cycle.supportImage (Component.Image.inclusion X C) m p A = Component.Image.supportImage X C p A := by
  apply Subtype.ext
  apply irreducibleSetEquivPoints.injective
  exact (Cycle.image_point (Component.Image.inclusion X C) A.val).trans
    (Component.Image.supportImage_point X C p A).symm

theorem restrict_eq (C : irreducibleComponents X.carrier) (p : ℕ) :
    CycleMaps.restrict (Component.Image.inclusion X C) m p = Component.CycleMaps.restrict X C p := by
  apply LinearMap.ext
  intro a
  apply Finsupp.ext
  intro A
  rw [CycleMaps.restrict_apply, Component.CycleMaps.restrict_apply, supportImage_eq]

theorem embed_eq (C : irreducibleComponents X.carrier) (p : ℕ) :
    CycleMaps.embed (Component.Image.inclusion X C) m p = Component.CycleMaps.embed X C p := by
  rw [CycleMaps.embed_eq_pushforward, Component.CycleMaps.embed_eq_pushforward]

theorem sum_embed_restrict [Fintype (irreducibleComponents X.carrier)]
    (p : ℕ) (a : X.RationalDimensionCycle p) :
    ∑ C : irreducibleComponents X.carrier,
      CycleMaps.embed (Component.Image.inclusion X C) m p (CycleMaps.restrict (Component.Image.inclusion X C) m p a) = a := by
  simp only [embed_eq X m, restrict_eq X m]
  exact Component.Principal.CycleDecomposition.sum_embed_restrict X p a

theorem restrict_fundamental (C : irreducibleComponents X.carrier) :
    CycleMaps.restrict (Component.Image.inclusion X C) m 0 (ProperCycleLinearity.fundamentalCycle X) =
      ProperCycleLinearity.fundamentalCycle (X.componentVariety C).presentation := by
  ext A
  rw [CycleMaps.restrict_apply, ZeroComponents.fundamentalCycle_apply X m,
    ZeroComponents.fundamentalCycle_apply (X.componentVariety C).presentation m]

theorem sum_fundamental [Fintype (irreducibleComponents X.carrier)] :
    ∑ C : irreducibleComponents X.carrier,
      CycleMaps.embed (Component.Image.inclusion X C) m 0 (ProperCycleLinearity.fundamentalCycle (X.componentVariety C).presentation) =
      ProperCycleLinearity.fundamentalCycle X := by
  simp only [← restrict_fundamental X m]
  exact sum_embed_restrict X m 0 _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.ComponentMaps
