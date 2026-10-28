import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight

/-! # Adjacent Support Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk

noncomputable section

/-! Adjacent ambient codimensions give a one-dimensional support stalk,
for arbitrary singular integral supports in every ambient dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem coheight_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport r) (C : X.DimensionCycleSupport (r + 1))
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx) = 1 := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let : Algebra R T := σ.hom.toAlgebra
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  have hp : p.asIdeal.height = r := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact IntermediateSupports.support_coheight X m r A
  have hd : (IsLocalRing.maximalIdeal R).height = r + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using IntermediateSupports.stalk_height X m (r + 1) C
  have hq := Affine.DivisorDimension.quotient_dimension_add_height_le R p
  rw [hp, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R), hd] at hq
  have hq' : ringKrullDim (R ⧸ p.asIdeal) ≤ 1 := by
    apply (ENat.WithBot.add_le_add_natCast_left_iff (c := r)).mp
    simpa only [WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one] using hq
  have hσ : Function.Surjective (Algebra.ofId R T) :=
    Local.Principal.supportStalkMap_surjective X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  rw [he, ringKrullDim_stalk_eq_coheight] at hq'
  have hle : coheight y ≤ 1 := WithBot.coe_le_coe.mp hq'
  have hy : y ≠ genericPoint Y := by
    intro h
    have heq : CycleClass.Thom.IntersectionGeometry.supportPoint C.val = CycleClass.Thom.IntersectionGeometry.supportPoint A.val :=
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx).symm.trans
        ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι A.val) h).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq A.val))
    have hc := congrArg X.supportCodimension (irreducibleSetEquivPoints.injective heq)
    rw [C.property, A.property] at hc
    omega
  have hle' : y ≤ genericPoint Y := genericPoint_specializes y
  have hlt : y < genericPoint Y := lt_of_le_not_ge hle' (by
    intro h
    exact hy (Specializes.antisymm h hle').eq)
  have htop : coheight (genericPoint Y) = 0 := (isTop_top : IsTop (⊤ : Y)).isMax.coheight_eq_zero
  have hlo := coheight_add_one_le hlt
  rw [htop, zero_add] at hlo
  exact le_antisymm hle hlo

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk
