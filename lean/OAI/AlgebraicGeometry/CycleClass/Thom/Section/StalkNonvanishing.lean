import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalIntersectionCoefficient
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport

/-! # Stalk Nonvanishing -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions.StepIntersectionCoefficient

/-! The canonical section step has the original Serre--Tor coefficient
where the first support has the actual section germ as its stalk ideal.
The ambient open is arbitrary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalIntersectionCoefficient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

theorem parentFunction_eq_supportStalk_germ (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B) :
    Affine.SectionFunction.Constructions.parentSectionFunction D B s = algebraMap (D.scheme.presheaf.stalk (IntersectionGeometry.supportPreimage D.val x hxD))
      D.scheme.functionField (SupportStalkModule.Constructions.supportStalkMap V.carrier D.val x hxD (V.carrier.presheaf.germ B x hxB (B.topIso.hom s))) := by
  let : Nonempty (D.inclusion ⁻¹ᵁ B) :=
    ⟨⟨IntersectionGeometry.supportPreimage D.val x hxD, SupportSectionGerm.Constructions.supportPreimage_mem_open V.carrier D.val x hxD B hxB⟩⟩
  exact SupportSectionGerm.Constructions.restrictedFunction_eq_supportStalk_germ V.carrier D.val x hxD B hxB (B.topIso.hom s)

include hs in
theorem section_supportStalk_ne_zero (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B) :
    SupportStalkModule.Constructions.supportStalkMap V.carrier D.val x hxD (V.carrier.presheaf.germ B x hxB (B.topIso.hom s)) ≠ 0 := by
  intro hz
  apply hs
  exact (parentFunction_eq_supportStalk_germ D B s x hxD hxB).trans (by rw [hz, map_zero])

theorem intersectionMultiplicity_eq_stepCoefficient (A : IrreducibleCloseds V.carrier)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hxA : IntersectionGeometry.supportPoint C.val ∈ (A : Set V.carrier))
    (hxD : IntersectionGeometry.supportPoint C.val ∈ (D.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ B)
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap V.carrier A (IntersectionGeometry.supportPoint C.val) hxA).hom =
      Ideal.span {V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint C.val) hxB (B.topIso.hom s)}) :
    IntersectionGeometry.intersectionMultiplicity V.presentation A D.val C.val = CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C := by
  rw [CupPrincipalGeneral.Constructions.Step.principalStep_coefficient]
  apply PrincipalIntersectionCoefficient.Constructions.intersectionMultiplicity_eq_principalDivisorCoefficient_of_codimension
    V.presentation A D.val C.val hxA hxD _
    (V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint C.val) hxB (B.topIso.hom s)) hA
    (section_supportStalk_ne_zero D B s hs (IntersectionGeometry.supportPoint C.val) hxD hxB)
    (Affine.SectionFunction.Constructions.parentSectionFunction D B s) (parentFunction_eq_supportStalk_germ D B s (IntersectionGeometry.supportPoint C.val) hxD hxB)
  rw [Integral.ProductSupport.Constructions.integralPresentation_supportCodimension, Integral.ProductSupport.Constructions.integralPresentation_supportCodimension, D.property]
  exact C.property

end AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions.StepIntersectionCoefficient

namespace AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions

/-! Nonvanishing of a section on an original parent cycle is equivalent
to nonvanishing of its actual reduced-support germ at any retained point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions.StepIntersectionCoefficient OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

theorem parentFunction_ne_zero_iff (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B) :
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0 ↔
      SupportStalkModule.Constructions.supportStalkMap V.carrier D.val x hxD (V.carrier.presheaf.germ B x hxB (B.topIso.hom s)) ≠ 0 := by
  rw [StepIntersectionCoefficient.parentFunction_eq_supportStalk_germ D B s x hxD hxB]
  exact map_ne_zero_iff _ (IsFractionRing.injective _ _)

end AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions

end

end OAI
