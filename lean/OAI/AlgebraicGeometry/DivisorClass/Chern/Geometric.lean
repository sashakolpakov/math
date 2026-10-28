import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.AlgebraicGeometry.DivisorClass.Chern.Support
import OAI.AlgebraicGeometry.DivisorClass.Chern.Classes

/-! # Geometric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the line bundle's divisor in the existing geometric cycle grading

On an integral smooth projective carrier, the actual rational-section orders
give a finite integral cycle on precisely the dimension-graded codimension-one
supports used by the existing geometric cycle-class map. This module constructs
that geometric class; its equality with the logarithmic first Chern class is
not assumed and remains to be proved.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Geometric.Construction

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]

/-- A codimension-one point gives its genuine dimension-graded closed support. -/
def pointDivisorSupport (x : {x : X.carrier // Order.coheight x = 1}) : X.DimensionCycleSupport 1 := by
  refine ⟨irreducibleSetEquivPoints.symm x.val, ?_⟩
  let Z : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x.val
  have hc := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (X.componentInclusion (X.supportComponent Z)) X.structureMap
  rw [X.componentInclusion_over] at hc
  have hd := SupportCodimension.Construction.pointClosure_dimension_add_one X.structureMap x.val x.property
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent Z)).structureMap -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap = 1
  rw [hc]
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap + 1 =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap at hd
  omega

theorem pointDivisorSupport_injective : Function.Injective (pointDivisorSupport X) := by
  intro x y h
  apply Subtype.ext
  apply irreducibleSetEquivPoints.symm.injective
  exact congrArg Subtype.val h

end Geometric.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

/-- The rational section's divisor indexed by actual dimension-graded closed supports. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionIntegralDivisor : Classes.Construction.IntegralDivisor X :=
  Finsupp.mapDomain (Geometric.Construction.pointDivisorSupport X)
    (Finsupp.subtypeDomain (fun x : X.carrier => Order.coheight x = 1) L.rationalSectionPointDivisor)

/-- The multiplicity of each support is the actual order of the rational section. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionIntegralDivisor_apply
    (x : {x : X.carrier // Order.coheight x = 1}) :
    L.rationalSectionIntegralDivisor (Geometric.Construction.pointDivisorSupport X x) = L.rationalSectionOrder x.val := by
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionIntegralDivisor
  rw [Finsupp.mapDomain_apply_of_injective (Geometric.Construction.pointDivisorSupport_injective X)]
  rfl

/-- The independently constructed geometric class of the line bundle's divisor. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionGeometricClass : X.rationalCohomology 2 :=
  Classes.Construction.divisorGeometricClass X L.rationalSectionIntegralDivisor

theorem Line.Bundles.AlgebraicLineBundle.rationalSectionGeometricClass_eq :
    L.rationalSectionGeometricClass = X.geometricCycleClassMap 1
      (Classes.Construction.rationalizeDivisor X L.rationalSectionIntegralDivisor) := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
