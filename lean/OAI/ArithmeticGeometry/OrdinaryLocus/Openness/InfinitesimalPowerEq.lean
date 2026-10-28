import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupTangentsEq

/-! # Infinitesimal Power Eq -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InfinitesimalPowerEq.Construction.InfinitesimalPower

/-!
# Openness: multiplication in characteristic p on local infinitesimal group points

The reduction map is precomposition with the actual quotient scheme map.
Every point in its kernel is realized by the relative tangent module.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupTangentsEq.Construction.GroupTangents

variable {S : Scheme.{u}} {C : CommRingCat.{u}} [IsLocalRing C]
variable (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥)

noncomputable def reductionMap :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ s) ⟶ Over.mk s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) rfl

noncomputable def reduction (A : Over S) [MonObj A] :
    (Over.mk s ⟶ A) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ s) ⟶ A) where
  toFun a := reductionMap s J ≫ a
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

theorem reduction_overPoint (A : Over S) [MonObj A] (v : GroupTangentsEq.Construction.GroupTangents.relative s J hJ A) :
    reduction s J A (GroupTangentsEq.Construction.GroupTangents.overPoint s J hJ A v) = 1 := by
  apply Over.OverMorphism.ext
  have h := PointedTangentAt.Construction.PointedTangent.point_reduction J hJ (GroupTangentsEq.Construction.GroupTangents.unitPoint s A).hom v.val
  have he : reductionMap s J ≫ (1 : Over.mk s ⟶ A) = 1 := MonObj.comp_one _
  exact h.trans (congrArg (fun z => z.left) he)

/-- The relative tangent module covers precisely the identity fiber of the
actual reduction map on group-scheme points. -/
theorem exists_overPoint (A : Over S) [MonObj A] (a : Over.mk s ⟶ A)
    (ha : reduction s J A a = 1) :
    ∃ v : GroupTangentsEq.Construction.GroupTangents.relative s J hJ A, GroupTangentsEq.Construction.GroupTangents.overPoint s J hJ A v = a := by
  have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (GroupTangentsEq.Construction.GroupTangents.unitPoint s A).hom := by
    exact congrArg (fun z => z.left) (ha.trans (map_one (reduction s J A)).symm)
  obtain ⟨v, hv⟩ := PointedTangentAt.Construction.PointedTangent.exists_point J hJ (GroupTangentsEq.Construction.GroupTangents.unitPoint s A).hom a.left hred
  have hv' : GroupTangentsEq.Construction.GroupTangents.point s J hJ A v = a.left := hv
  have hker : v ∈ GroupTangentsEq.Construction.GroupTangents.relative s J hJ A := by
    change GroupTangentsEq.Construction.GroupTangents.tangent s J hJ (CategoryTheory.CartesianMonoidalCategory.toUnit A) v = 0
    apply GroupTangentsEq.Construction.GroupTangents.point_injective s J hJ (𝟙_ (Over S))
    rw [GroupTangentsEq.Construction.GroupTangents.point_tangent, GroupTangentsEq.Construction.GroupTangents.point_zero, hv']
    exact Over.w a
  refine ⟨⟨v, hker⟩, ?_⟩
  apply Over.OverMorphism.ext
  exact hv'

include hJ in
/-- Multiplication by the characteristic kills every first-order point
that reduces to the group identity. -/
theorem pow_eq_one_of_reduction_eq_one
    (A : Over S) [MonObj A] [IsCommMonObj A]
    (p : ℕ) [CharP C p] (a : Over.mk s ⟶ A)
    (ha : reduction s J A a = 1) : a ^ p = 1 := by
  obtain ⟨v, rfl⟩ := exists_overPoint s J hJ A a ha
  rw [← GroupTangentsEq.Construction.GroupTangents.overPoint_natCast_smul, CharP.cast_eq_zero C p, zero_smul, GroupTangentsEq.Construction.GroupTangents.overPoint_zero]

include hJ in
/-- First-order lifts with the same reduction have the same p-th power
in characteristic p. -/
theorem pow_eq_of_reduction_eq
    (A : Over S) [GrpObj A] [IsCommMonObj A]
    (p : ℕ) [CharP C p] (a b : Over.mk s ⟶ A)
    (hab : reduction s J A a = reduction s J A b) : a ^ p = b ^ p := by
  have hred : reduction s J A (a / b) = 1 := by rw [map_div, hab, div_self']
  have h := pow_eq_one_of_reduction_eq_one s J hJ A p (a / b) hred
  rw [div_pow, div_eq_one] at h
  exact h

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InfinitesimalPowerEq.Construction.InfinitesimalPower
