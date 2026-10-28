import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalUnramified
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi

/-! # Power -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power.PowerGeometry

/-!
# TorsionQuotient: global unramifiedness and finiteness of prime-to-characteristic torsion

The local power-lifting argument is applied to every source stalk. Properness
of the actual torsion equalizer then gives finiteness by the finite-fiber
criterion. No affine hypothesis on the group or base is imposed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))

include hn in
theorem unit_on_local_test {C : CommRingCat.{u}} [IsLocalRing C] (s : Spec C ⟶ S) :
    IsUnit (n : C) := by
  simpa only [map_natCast] using
    (hn (s (IsLocalRing.closedPoint C))).map (Scheme.stalkClosedPointTo s).hom

include hn in
/-- Multiplication by a base unit on any commutative group scheme is
formally unramified, proved using actual local infinitesimal scheme points. -/
theorem power_formallyUnramified : FormallyUnramified (((𝟙 A : A ⟶ A) ^ n).left) := by
  apply LocalUnramified.LocalUnramifiedCriterion.of_local_hom_ext
  intro C hC J hJ a b hred hp
  let s := a ≫ A.hom
  have hb : b ≫ A.hom = s := by
    have h := congrArg (fun z => z ≫ A.hom) hp
    simpa only [Category.assoc, Over.w] using h.symm
  let α : Over.mk s ⟶ A := Over.homMk a rfl
  let β : Over.mk s ⟶ A := Over.homMk b hb
  have hp' : α ^ n = β ^ n := by
    apply Over.OverMorphism.ext
    change (α ≫ (𝟙 A : A ⟶ A) ^ n).left = (β ≫ (𝟙 A : A ⟶ A) ^ n).left at hp
    simpa only [MonObj.comp_pow, Category.comp_id] using hp
  have hred' : LocalPowerIn.LocalPower.reduction s J A α = LocalPowerIn.LocalPower.reduction s J A β := by
    apply Over.OverMorphism.ext
    exact hred
  have he := LocalPowerIn.LocalPower.power_lift_unique s J hJ A n (unit_on_local_test n hn s)
    α β hred' hp'
  exact congrArg (fun z : Over.mk s ⟶ A => z.left) he

include hn in
/-- The actual torsion equalizer of a proper commutative group scheme is
formally unramified when the integer is invertible on the base. -/
theorem torsion_formallyUnramified [IsProper A.hom] :
    FormallyUnramified (SubgroupFunctor.torsionScheme A n).hom := by
  let : IsClosedImmersion (SubgroupFunctor.torsionι A n).left := Quasi.TorsionGeometry.torsion_closedImmersion A n
  let : FormallyUnramified (((𝟙 A : A ⟶ A) ^ n).left) := power_formallyUnramified A n hn
  have he : (SubgroupFunctor.torsionι A n).left ≫ ((𝟙 A : A ⟶ A) ^ n).left =
      (SubgroupFunctor.torsionScheme A n).hom ≫ η[A].left := by
    have h := equalizer.condition ((𝟙 A : A ⟶ A) ^ n) (1 : A ⟶ A)
    have h' := congrArg (fun z : SubgroupFunctor.torsionScheme A n ⟶ A => z.left) h
    change (SubgroupFunctor.torsionι A n).left ≫ ((𝟙 A : A ⟶ A) ^ n).left =
      (SubgroupFunctor.torsionι A n).left ≫ (1 : A ⟶ A).left at h'
    calc
      _ = (SubgroupFunctor.torsionι A n).left ≫ (1 : A ⟶ A).left := h'
      _ = _ := by
        change (SubgroupFunctor.torsionι A n).left ≫ (A.hom ≫ η[A].left) = _
        rw [← Category.assoc, Over.w]
  have hu : FormallyUnramified ((SubgroupFunctor.torsionι A n).left ≫ ((𝟙 A : A ⟶ A) ^ n).left) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  rw [he] at hu
  let : FormallyUnramified ((SubgroupFunctor.torsionScheme A n).hom ≫ η[A].left) := hu
  exact FormallyUnramified.of_comp (SubgroupFunctor.torsionScheme A n).hom η[A].left

include hn in
/-- Prime-to-characteristic torsion in a proper commutative group scheme is
finite over the base. Smoothness and connectedness are not needed here. -/
theorem torsion_isFinite [IsProper A.hom] : IsFinite (SubgroupFunctor.torsionScheme A n).hom := by
  let : IsProper (SubgroupFunctor.torsionScheme A n).hom := Quasi.TorsionGeometry.torsion_isProper A n
  let : FormallyUnramified (SubgroupFunctor.torsionScheme A n).hom := torsion_formallyUnramified A n hn
  exact Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power.PowerGeometry
