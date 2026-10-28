import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport

/-! # Divisor Descent -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.DivisorDescent

noncomputable section

section

/-! The faithfully defined principal-divisor relations in codimension one
are annihilated by the actual geometric class map, on every presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisor.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)

/-- The coefficient vanishes in every other actual component. -/
theorem principalDivisorCoefficient_other_component (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (C : irreducibleComponents X.carrier) (hC : C ≠ X.supportComponent W)
    (Z : IrreducibleCloseds (X.componentVariety C).carrier) :
    IntersectionGeometry.principalDivisorCoefficient X W g (X.componentSupportImage C Z) = 0 := by
  have hout : IntersectionGeometry.supportPoint (X.componentSupportImage C Z) ∉ (W : Set X.carrier) := by
    intro hxW
    let x := IntersectionGeometry.supportPoint (X.componentSupportImage C Z)
    have hxC : x ∈ C.val := X.componentSupportImage_subset C Z
      ((X.componentSupportImage C Z).isIrreducible.isGenericPoint_genericPoint
        (X.componentSupportImage C Z).isClosed).mem
    have hxD : x ∈ (X.supportComponent W).val := X.support_subset_component W hxW
    let := X.stalk_isDomain x
    exact hC (Subtype.ext (Foundations.Scheme.LocalDomainComponents.irreducibleComponents_eq_of_mem_of_stalkDomain x
      C.property (X.supportComponent W).property hxC hxD))
  simp only [IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hout]

/-- On its component the same coefficient is the order of the actual
function pulled through the canonical reduced-support isomorphism. -/
theorem principalDivisorCoefficient_component (hW : X.supportCodimension W = 0)
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (Z : IrreducibleCloseds (X.componentVariety (X.supportComponent W)).carrier) :
    IntersectionGeometry.principalDivisorCoefficient X W g (X.componentSupportImage (X.supportComponent W) Z) =
      ((X.componentVariety (X.supportComponent W)).carrier.ord
        (RationalOrderTransport.Constructions.openFunctionFieldMap (CodimensionZeroSupport.Constructions.componentReducedSupportIso X W hW).hom g) (IntersectionGeometry.supportPoint Z) : ℚ) := by
  let e := CodimensionZeroSupport.Constructions.componentReducedSupportIso X W hW
  have hx : Geometric.GenericPoint.reducedSupportι W (e.hom (IntersectionGeometry.supportPoint Z)) =
      IntersectionGeometry.supportPoint (X.componentSupportImage (X.supportComponent W) Z) := by
    have h := congrArg (fun k : (X.componentVariety (X.supportComponent W)).carrier ⟶ X.carrier =>
      k (IntersectionGeometry.supportPoint Z)) (CodimensionZeroSupport.Constructions.componentReducedSupportIso_inclusion X W hW)
    exact h.trans (X.componentSupportImage_genericPoint (X.supportComponent W) Z).symm
  rw [IntersectionGeometry.principalDivisorCoefficient_at_image X W g _ (e.hom (IntersectionGeometry.supportPoint Z)) hx]
  exact congrArg (fun n : ℤ => (n : ℚ)) (RationalOrderTransport.Constructions.ord_openImmersion e.hom g (IntersectionGeometry.supportPoint Z)).symm

theorem isPrincipalDivisor_geometricClass_zero (d : X.RationalDimensionCycle 1)
    (hd : IntersectionGeometry.IsPrincipalDivisor X 1 d) : X.geometricCycleClassMap 1 d = 0 := by
  obtain ⟨W, hW, g, hg, hcoeff⟩ := hd
  have hW0 : X.supportCodimension W = 0 := by omega
  apply (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
  funext C
  have hc : X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 (X.geometricCycleClassMap 1 d) C =
      (X.componentVariety C).geometricCycleClassMap 1 (X.componentDimensionCycleEquiv 1 d C) :=
    X.componentBettiEquiv_geometricCycleClassMap 1 d C
  rw [hc, map_zero, Pi.zero_apply]
  by_cases hC : C = X.supportComponent W
  · subst C
    let f := RationalOrderTransport.Constructions.openFunctionFieldMap (CodimensionZeroSupport.Constructions.componentReducedSupportIso X W hW0).hom g
    have hf : f ≠ 0 := (map_ne_zero_iff _ (RationalOrderTransport.Constructions.openFunctionFieldMap
      (CodimensionZeroSupport.Constructions.componentReducedSupportIso X W hW0).hom).hom.injective).mpr hg
    apply PrincipalDivisor.Constructions.geometricClass_zero_of_principal_orders (X.componentVariety (X.supportComponent W)) f hf
    intro Z
    rw [X.componentDimensionCycleEquiv_apply, hcoeff]
    exact principalDivisorCoefficient_component X W hW0 g Z.val
  · have hz : X.componentDimensionCycleEquiv 1 d C = 0 := by
      ext Z
      rw [X.componentDimensionCycleEquiv_apply, hcoeff, Finsupp.zero_apply]
      exact principalDivisorCoefficient_other_component X W g C hC Z.val
    rw [hz, map_zero]

theorem rationalEquivalences_le_geometricClass_ker :
    IntersectionGeometry.rationalEquivalences X 1 ≤ LinearMap.ker (X.geometricCycleClassMap 1) := by
  apply Submodule.span_le.mpr
  intro d hd
  exact isPrincipalDivisor_geometricClass_zero X d hd

theorem geometricClass_eq_of_rationallyEquivalent {a b : X.RationalDimensionCycle 1}
    (h : IntersectionGeometry.RationallyEquivalent X 1 a b) : X.geometricCycleClassMap 1 a = X.geometricCycleClassMap 1 b := by
  have hz := rationalEquivalences_le_geometricClass_ker X h
  change X.geometricCycleClassMap 1 (a - b) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end Constructions

end

/-! Principal-divisor coefficients restrict to a component through the actual
isomorphism of reduced support schemes and its actual function-field map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.PrincipalComponentRestriction
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
  (W : IrreducibleCloseds (X.componentVariety C).carrier)

/-- The coefficient comparison is valid for every irreducible test support. -/
theorem principalDivisorCoefficient_componentImage
    (g : (Geometric.GenericPoint.reducedSupportScheme (X.componentSupportImage C W)).functionField)
    (Z : IrreducibleCloseds (X.componentVariety C).carrier) :
    IntersectionGeometry.principalDivisorCoefficient X (X.componentSupportImage C W) g (X.componentSupportImage C Z) =
      IntersectionGeometry.principalDivisorCoefficient (X.componentVariety C).presentation W
        (RationalOrderTransport.Constructions.openFunctionFieldMap (X.componentSupportSchemeIso C W).hom g) Z := by
  let e := X.componentSupportSchemeIso C W
  by_cases hz : IntersectionGeometry.supportPoint Z ∈ (W : Set (X.componentVariety C).carrier)
  · let x := IntersectionGeometry.supportPreimage W (IntersectionGeometry.supportPoint Z) hz
    have hx : Geometric.GenericPoint.reducedSupportι W x = IntersectionGeometry.supportPoint Z := IntersectionGeometry.supportPreimage_spec W (IntersectionGeometry.supportPoint Z) hz
    have hxy : Geometric.GenericPoint.reducedSupportι (X.componentSupportImage C W) (e.hom x) =
        IntersectionGeometry.supportPoint (X.componentSupportImage C Z) := by
      have h := congrArg (fun k : Geometric.GenericPoint.reducedSupportScheme W ⟶ X.carrier => k x)
        (X.componentSupportSchemeIso_hom_inclusion C W)
      exact h.trans ((congrArg (X.componentInclusion C) hx).trans
        (X.componentSupportImage_genericPoint C Z).symm)
    rw [IntersectionGeometry.principalDivisorCoefficient_at_image X _ g _ (e.hom x) hxy,
      IntersectionGeometry.principalDivisorCoefficient_at_image (X.componentVariety C).presentation W _ Z x hx]
    exact congrArg (fun n : ℤ => (n : ℚ)) (RationalOrderTransport.Constructions.ord_openImmersion e.hom g x).symm
  · have hout : IntersectionGeometry.supportPoint (X.componentSupportImage C Z) ∉
        (X.componentSupportImage C W : Set X.carrier) := by
      intro h
      change IntersectionGeometry.supportPoint (X.componentSupportImage C Z) ∈
        X.componentInclusion C '' (W : Set (X.componentVariety C).carrier) at h
      rw [show IntersectionGeometry.supportPoint (X.componentSupportImage C Z) = X.componentInclusion C (IntersectionGeometry.supportPoint Z) from
        X.componentSupportImage_genericPoint C Z] at h
      obtain ⟨x, hx, he⟩ := h
      exact hz ((X.componentInclusion C).isClosedEmbedding.injective he ▸ hx)
    simp only [IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hout, dite_eq_right hz]

end Constructions.PrincipalComponentRestriction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.DivisorDescent
