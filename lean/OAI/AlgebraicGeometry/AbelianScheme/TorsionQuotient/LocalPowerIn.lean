import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.GroupTangentsEq

/-! # Local Power In -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower

/-!
# TorsionQuotient: multiplication by a unit on local infinitesimal group points

The reduction map is precomposition with the actual quotient scheme map.
Every point in its kernel is realized by the relative tangent module.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents

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

theorem reduction_overPoint (A : Over S) [MonObj A] (v : GroupTangentsEq.GroupTangents.relative s J hJ A) :
    reduction s J A (GroupTangentsEq.GroupTangents.overPoint s J hJ A v) = 1 := by
  apply Over.OverMorphism.ext
  have h := PointedTangentAt.PointedTangent.point_reduction J hJ (GroupTangentsEq.GroupTangents.unitPoint s A).hom v.val
  have he : reductionMap s J ≫ (1 : Over.mk s ⟶ A) = 1 := MonObj.comp_one _
  exact h.trans (congrArg (fun z => z.left) he)

/-- The relative tangent module covers precisely the identity fiber of the
actual reduction map on group-scheme points. -/
theorem exists_overPoint (A : Over S) [MonObj A] (a : Over.mk s ⟶ A)
    (ha : reduction s J A a = 1) :
    ∃ v : GroupTangentsEq.GroupTangents.relative s J hJ A, GroupTangentsEq.GroupTangents.overPoint s J hJ A v = a := by
  have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (GroupTangentsEq.GroupTangents.unitPoint s A).hom := by
    exact congrArg (fun z => z.left) (ha.trans (map_one (reduction s J A)).symm)
  obtain ⟨v, hv⟩ := PointedTangentAt.PointedTangent.exists_point J hJ (GroupTangentsEq.GroupTangents.unitPoint s A).hom a.left hred
  have hv' : GroupTangentsEq.GroupTangents.point s J hJ A v = a.left := hv
  have hker : v ∈ GroupTangentsEq.GroupTangents.relative s J hJ A := by
    change GroupTangentsEq.GroupTangents.tangent s J hJ (CategoryTheory.CartesianMonoidalCategory.toUnit A) v = 0
    apply GroupTangentsEq.GroupTangents.point_injective s J hJ (𝟙_ (Over S))
    rw [GroupTangentsEq.GroupTangents.point_tangent, GroupTangentsEq.GroupTangents.point_zero, hv']
    exact Over.w a
  refine ⟨⟨v, hker⟩, ?_⟩
  apply Over.OverMorphism.ext
  exact hv'

theorem tangent_power_injective (A : Over S) [MonObj A] [IsCommMonObj A]
    (n : ℕ) (hn : IsUnit (n : C)) (v w : GroupTangentsEq.GroupTangents.relative s J hJ A)
    (h : GroupTangentsEq.GroupTangents.overPoint s J hJ A v ^ n = GroupTangentsEq.GroupTangents.overPoint s J hJ A w ^ n) : v = w := by
  have he : (n : C) • v = (n : C) • w := by
    apply GroupTangentsEq.GroupTangents.overPoint_injective s J hJ A
    rwa [GroupTangentsEq.GroupTangents.overPoint_natCast_smul, GroupTangentsEq.GroupTangents.overPoint_natCast_smul]
  obtain ⟨r, hr⟩ := hn
  have hi := congrArg (fun z => ((↑r⁻¹ : C) • z)) he
  simpa only [← hr, smul_smul, Units.inv_mul, one_smul] using hi

theorem exists_tangent_root (A : Over S) [MonObj A] [IsCommMonObj A]
    (n : ℕ) (hn : IsUnit (n : C)) (v : GroupTangentsEq.GroupTangents.relative s J hJ A) :
    ∃ w : GroupTangentsEq.GroupTangents.relative s J hJ A, GroupTangentsEq.GroupTangents.overPoint s J hJ A w ^ n = GroupTangentsEq.GroupTangents.overPoint s J hJ A v := by
  obtain ⟨r, hr⟩ := hn
  refine ⟨(↑r⁻¹ : C) • v, ?_⟩
  rw [← GroupTangentsEq.GroupTangents.overPoint_natCast_smul, ← hr, smul_smul, Units.mul_inv, one_smul]

include hJ in
/-- Multiplication by an invertible integer is injective in the actual
infinitesimal identity fiber, with no affine hypothesis on the group. -/
theorem power_injective_in_kernel (A : Over S) [MonObj A] [IsCommMonObj A]
    (n : ℕ) (hn : IsUnit (n : C)) (a b : Over.mk s ⟶ A)
    (ha : reduction s J A a = 1) (hb : reduction s J A b = 1)
    (hab : a ^ n = b ^ n) : a = b := by
  obtain ⟨v, rfl⟩ := exists_overPoint s J hJ A a ha
  obtain ⟨w, rfl⟩ := exists_overPoint s J hJ A b hb
  exact congrArg (GroupTangentsEq.GroupTangents.overPoint s J hJ A) (tangent_power_injective s J hJ A n hn v w hab)

include hJ in
/-- Actual infinitesimal points have unique nth roots when n is a base unit. -/
theorem exists_unique_root_in_kernel (A : Over S) [MonObj A] [IsCommMonObj A]
    (n : ℕ) (hn : IsUnit (n : C)) (a : Over.mk s ⟶ A)
    (ha : reduction s J A a = 1) :
    ∃! b : Over.mk s ⟶ A, reduction s J A b = 1 ∧ b ^ n = a := by
  obtain ⟨v, rfl⟩ := exists_overPoint s J hJ A a ha
  obtain ⟨w, hw⟩ := exists_tangent_root s J hJ A n hn v
  refine ⟨GroupTangentsEq.GroupTangents.overPoint s J hJ A w, ⟨reduction_overPoint s J hJ A w, hw⟩, ?_⟩
  intro b hb
  exact power_injective_in_kernel s J hJ A n hn b (GroupTangentsEq.GroupTangents.overPoint s J hJ A w)
    hb.1 (reduction_overPoint s J hJ A w) (hb.2.trans hw.symm)

include hJ in
/-- Two arbitrary local group points with the same reduction and nth power
are equal. Translation reduces this to the infinitesimal identity fiber. -/
theorem power_lift_unique (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : IsUnit (n : C)) (a b : Over.mk s ⟶ A)
    (hred : reduction s J A a = reduction s J A b) (hp : a ^ n = b ^ n) : a = b := by
  have hk : reduction s J A (a / b) = 1 := by rw [map_div, hred, div_self']
  have hpow : (a / b) ^ n = (1 : Over.mk s ⟶ A) ^ n := by rw [div_pow, hp, div_self', one_pow]
  have hab := power_injective_in_kernel s J hJ A n hn (a / b) 1 hk
    (map_one _) hpow
  exact div_eq_one.mp hab

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower
