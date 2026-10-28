import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk

/-! # Support Surface Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.SupportSurfaceStalk

noncomputable section

/-! Two steps of ambient codimension give a two-dimensional local
domain on the larger support, including singular and nonnormal supports
in every ambient dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m

theorem coheight_two (W : X.DimensionCycleSupport r) (A : X.DimensionCycleSupport (r + 1))
    (C : X.DimensionCycleSupport (r + 2)) (hAW : A.val ≤ W.val)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier)) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW) = 2 := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  let : Algebra R T := σ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  have hp : p.asIdeal.height = r := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact IntermediateSupports.support_coheight X m r W
  have hq := Affine.DivisorDimension.quotient_dimension_add_height_le R p
  rw [hp, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R),
    IntermediateSupports.stalk_height X m (r + 2) C] at hq
  have hq' : ringKrullDim (R ⧸ p.asIdeal) ≤ 2 := by
    apply (ENat.WithBot.add_le_add_natCast_left_iff (c := r)).mp
    simpa only [Nat.cast_add, Nat.cast_ofNat, WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_ofNat] using hq
  have hσ : Function.Surjective (Algebra.ofId R T) :=
    Local.Principal.supportStalkMap_surjective X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  rw [he, ringKrullDim_stalk_eq_coheight] at hq'
  have hle : coheight y ≤ 2 := WithBot.coe_le_coe.mp hq'
  have hzW : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W.val : Set X.carrier) :=
    hAW (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  let z := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hzW
  have hz : coheight z = 1 := AdjacentSupportStalk.coheight_one X m r W A hzW
  have hyz : y ≤ z := by
    change z ⤳ y
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.isInducing.specializes_iff.mp
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).specializes hxA
  have hne : y ≠ z := by
    intro h
    have hh := congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W.val) h
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec] at hh
    have hc := congrArg X.supportCodimension (irreducibleSetEquivPoints.injective hh)
    rw [C.property, A.property] at hc
    omega
  have hlt : y < z := lt_of_le_not_ge hyz (by
    intro h
    exact hne (Specializes.antisymm h hyz).eq)
  have hlo := coheight_add_one_le hlt
  rw [hz, one_add_one_eq_two] at hlo
  exact le_antisymm hle hlo

theorem maximal_height (W : X.DimensionCycleSupport r) (A : X.DimensionCycleSupport (r + 1))
    (C : X.DimensionCycleSupport (r + 2)) (hAW : A.val ≤ W.val)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier)) :
    (IsLocalRing.maximalIdeal ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW))).height = 2 := by
  apply WithBot.coe_injective
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight,
    coheight_two X m r W A C hAW hxA hxW]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.SupportSurfaceStalk
