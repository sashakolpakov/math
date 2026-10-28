import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

/-! # Image -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

noncomputable section

/-! Actual integral component presentations preserve the native
codimension grading and inherit the ambient smooth relative dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem integral_codimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier) :
    V.presentation.supportCodimension W = CycleClass.Geometric.DimensionCycles.dimensionCodimension V W := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (V.presentation.componentInclusion (V.presentation.supportComponent W)) V.structureMap
  rw [V.presentation.componentInclusion_over] at h
  exact congrArg (fun n => n - Foundations.Scheme.SupportDimension.supportTranscendenceDimension W V.structureMap) h

theorem component_relativeDimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := by
  have h := smoothOfRelativeDimension_comp 0 m (X.componentInclusion C) X.structureMap
  simpa only [zero_add, X.componentInclusion_over] using h

theorem image_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (W : IrreducibleCloseds (X.componentVariety C).carrier) :
    X.supportCodimension (X.componentSupportImage C W) =
      (X.componentVariety C).presentation.supportCodimension W := by
  rw [X.supportCodimension_componentSupportImage, integral_codimension]

def supportImage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) (p : ℕ)
    (W : (X.componentVariety C).presentation.DimensionCycleSupport p) : X.DimensionCycleSupport p :=
  ⟨X.componentSupportImage C W.val, (image_codimension X C W.val).trans W.property⟩

theorem supportImage_injective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) : Function.Injective (supportImage X C p) := by
  intro A B h
  exact Subtype.ext (X.componentSupportImage_injective C (congrArg Subtype.val h))

def supportPreimage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) (p : ℕ)
    (W : X.DimensionCycleSupport p) (hW : (W.val : Set X.carrier) ⊆ C.val) :
    (X.componentVariety C).presentation.DimensionCycleSupport p :=
  ⟨X.componentSupportPreimage C W.val hW, by
    rw [← image_codimension, X.componentSupportImage_preimage, W.property]⟩

theorem supportImage_preimage (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (W : X.DimensionCycleSupport p) (hW : (W.val : Set X.carrier) ⊆ C.val) :
    supportImage X C p (supportPreimage X C p W hW) = W :=
  Subtype.ext (X.componentSupportImage_preimage C W.val hW)

theorem supportImage_point (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (W : (X.componentVariety C).presentation.DimensionCycleSupport p) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (supportImage X C p W).val = X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) :=
  X.componentSupportImage_genericPoint C W.val

def inclusion (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    (X.componentVariety C).toOver ⟶ X.toOver :=
  Over.homMk (X.componentInclusion C) (X.componentInclusion_over C)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image
