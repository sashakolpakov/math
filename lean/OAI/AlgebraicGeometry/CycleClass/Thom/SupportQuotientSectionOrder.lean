import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkSectionOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.FunctionOrderTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm

/-! # Support Quotient Section Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientSectionOrder.Constructions

noncomputable section

/-! The affine orders in the actual ambient prime quotient are exactly
the original geometric principal-divisor coefficients of a section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkSectionOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.FunctionOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme) [IsLocallyNoetherian X] (D : IrreducibleCloseds X) (x : X) (hxD : x ∈ (D : Set X))
  (B : X.Opens) [Nonempty ((Geometric.GenericPoint.reducedSupportι D) ⁻¹ᵁ B)] (hxB : x ∈ B) (s : Γ(X, B))

theorem ord_quotientSection (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))) :
    (Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))).ord
      (Affine.PrincipalSchemeOrder.Constructions.affineFunction (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD)
        (algebraMap (X.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD) (X.presheaf.germ B x hxB s))) q =
    (Geometric.GenericPoint.reducedSupportScheme D).ord
      ((Geometric.GenericPoint.reducedSupportScheme D).germToFunctionField ((Geometric.GenericPoint.reducedSupportι D) ⁻¹ᵁ B) ((Geometric.GenericPoint.reducedSupportι D).app B s))
      (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap X D x hxD q) := by
  let y := IntersectionGeometry.supportPreimage D x hxD
  let S := (Geometric.GenericPoint.reducedSupportScheme D).presheaf.stalk y
  let Q := StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD
  let e := StalkPrimeQuotient.Constructions.SupportScheme.quotientStalkEquiv X D x hxD
  let z := (Spec.map e.symm.toCommRingCatIso.hom) q
  let r := X.presheaf.germ B x hxB s
  have he := Affine.FunctionOrderTransport.Constructions.ord_affineFunction_equiv S Q e.symm (SupportStalkModule.Constructions.supportStalkMap X D x hxD r) q
  have hg := ConcreteCategory.congr_hom (SupportSectionGerm.Constructions.supportStalkMap_germ X D x hxD B hxB) s
  have hs := FromStalkSectionOrder.Constructions.ord_stalkSection (Geometric.GenericPoint.reducedSupportScheme D) y ((Geometric.GenericPoint.reducedSupportι D) ⁻¹ᵁ B)
    (SupportSectionGerm.Constructions.supportPreimage_mem_open X D x hxD B hxB) ((Geometric.GenericPoint.reducedSupportι D).app B s) z
  exact (congrArg (fun t => (Spec (.of Q)).ord (Affine.PrincipalSchemeOrder.Constructions.affineFunction Q t) q)
      (StalkPrimeQuotient.Constructions.SupportScheme.quotientStalkEquiv_symm_apply X D x hxD r)).symm.trans
    (he.trans ((congrArg (fun t => (Spec (.of S)).ord (Affine.PrincipalSchemeOrder.Constructions.affineFunction S t) z) hg).trans hs))

theorem principalCoefficient_quotientSupport (T : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds T.carrier) (z : T.carrier) (hzW : z ∈ (W : Set T.carrier))
    (U : T.carrier.Opens) [Nonempty ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)] (hzU : z ∈ U) (t : Γ(T.carrier, U))
    (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing T.carrier W z hzW))) :
    ((Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing T.carrier W z hzW))).ord
      (Affine.PrincipalSchemeOrder.Constructions.affineFunction (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing T.carrier W z hzW)
        (algebraMap (T.carrier.presheaf.stalk z) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing T.carrier W z hzW)
          (T.carrier.presheaf.germ U z hzU t))) q : ℚ) =
    IntersectionGeometry.principalDivisorCoefficient T W
      ((Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U) ((Geometric.GenericPoint.reducedSupportι W).app U t))
      (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport T.carrier W z hzW q) := by
  rw [IntersectionGeometry.principalDivisorCoefficient, dite_eq_left (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport_mem_parent T.carrier W z hzW q)]
  apply congrArg (fun n : ℤ => (n : ℚ))
  exact (ord_quotientSection T.carrier W z hzW U hzU t q).trans
    (congrArg ((Geometric.GenericPoint.reducedSupportScheme W).ord
      ((Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U) ((Geometric.GenericPoint.reducedSupportι W).app U t)))
      (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport_preimage T.carrier W z hzW q))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientSectionOrder.Constructions
