import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.RelativeHeight

/-! # Adjacent Support Coheight -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight

noncomputable section

/-! A codimension-two point on a codimension-one integral support has
codimension one in that support, without ambient smoothness or normality. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem coheight_one (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (W : IrreducibleCloseds X) (hW : coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1)
    (x : X) (hx : coheight x = 2) (hxW : x ∈ (W : Set X)) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW) = 1 := by
  let R := X.presheaf.stalk x
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X W x hxW
  let : Algebra R T := σ.hom.toAlgebra
  let p := Stalk.PrimeQuotient.kernelPrime X W x hxW
  have hp : p.asIdeal.height = 1 := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image, hW]
  have hdim : (IsLocalRing.maximalIdeal R).height = 2 := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight, hx]
  have hq := Affine.DivisorDimension.quotient_dimension_add_height_le R p
  rw [hp, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R), hdim] at hq
  have hq' : ringKrullDim (R ⧸ p.asIdeal) ≤ 1 := by
    apply (ENat.WithBot.add_le_add_natCast_left_iff (c := 1)).mp
    convert hq using 1 <;> norm_num
  have hσ : Function.Surjective (Algebra.ofId R T) := Local.Principal.supportStalkMap_surjective X W x hxW
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  rw [he, ringKrullDim_stalk_eq_coheight] at hq'
  have hle : coheight y ≤ 1 := WithBot.coe_le_coe.mp hq'
  have hy : y ≠ genericPoint Y := by
    intro h
    have heq : x = CycleClass.Thom.IntersectionGeometry.supportPoint W := (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hxW).symm.trans
      ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W) h).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))
    rw [heq, hW] at hx
    exact (by decide : (1 : ℕ∞) ≠ 2) hx
  have hle' : y ≤ genericPoint Y := genericPoint_specializes y
  have hlt : y < genericPoint Y := lt_of_le_not_ge hle' (by
    intro h
    exact hy (Specializes.antisymm h hle').eq)
  have htop : coheight (genericPoint Y) = 0 := (isTop_top : IsTop (⊤ : Y)).isMax.coheight_eq_zero
  have hlo := coheight_add_one_le hlt
  rw [htop, zero_add] at hlo
  exact le_antisymm hle hlo

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight
