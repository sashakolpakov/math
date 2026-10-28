import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension

/-! # Relative Height -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.RelativeHeight

noncomputable section

/-! An ambient codimension-two point lying on a divisor has native
codimension one inside the reduced divisor, including singular divisors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem supportPreimage_coheight (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx) = 1 := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let : Algebra R T := σ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  have hp : p.asIdeal.height = 1 := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact CurveSupports.coheight_one X m A
  have hCA : C.val ≤ A.val :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(A.val : Set X.carrier), A.val.isClosed⟩ : Closeds X.carrier) C.val).mp hx
  have hdim : (IsLocalRing.maximalIdeal R).height = 2 :=
    Stalk.maximalIdeal_height_two X m A C hCA
  have hq := Affine.DivisorDimension.quotient_dimension_add_height_le R p
  rw [hp, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R), hdim] at hq
  have hq' : ringKrullDim (R ⧸ p.asIdeal) ≤ 1 := by
    apply (ENat.WithBot.add_le_add_natCast_left_iff (c := 1)).mp
    convert hq using 1 <;> norm_num
  have hσ : Function.Surjective (Algebra.ofId R T) :=
    Local.Principal.supportStalkMap_surjective X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T :=
    (Ideal.quotientKerAlgEquivOfSurjective hσ).toRingEquiv.ringKrullDim
  rw [he, ringKrullDim_stalk_eq_coheight] at hq'
  have hle : coheight y ≤ 1 := WithBot.coe_le_coe.mp hq'
  have hy : y ≠ genericPoint Y := by
    intro h
    have heq : CycleClass.Thom.IntersectionGeometry.supportPoint C.val = CycleClass.Thom.IntersectionGeometry.supportPoint A.val :=
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx).symm.trans
        ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι A.val) h).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq A.val))
    have hAC : C.val = A.val := irreducibleSetEquivPoints.injective heq
    have hd := congrArg X.supportCodimension hAC
    rw [C.property, A.property] at hd
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

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.RelativeHeight
