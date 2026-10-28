import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Surjective Reduction Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SurjectiveReductionEq.SurjectiveReduction

/-!
# TorsionQuotient: replacing a surjective test-ring map by its kernel quotient

The two reduction conditions are equivalent by the actual quotient-kernel
isomorphism. This transports the checked infinitesimal-root construction
to arbitrary square-zero surjections of local test rings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem quotient_precomp_eq_iff {C B : CommRingCat.{u}} (p : C ⟶ B)
    (hp : Function.Surjective p) {X : Scheme.{u}} (a b : Spec C ⟶ X) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker p.hom))) ≫ a =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker p.hom))) ≫ b ↔
      Spec.map p ≫ a = Spec.map p ≫ b := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker p.hom))
  let k := CommRingCat.ofHom (RingHom.kerLift p.hom)
  have hqk : q ≫ k = p := by ext r; rfl
  let j := CommRingCat.ofHom (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
  have hpj : p ≫ j = q := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_symm_apply hp r
  constructor
  · intro h
    rw [← hqk, Spec.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun z => Spec.map k ≫ z) h
  · intro h
    change Spec.map q ≫ a = Spec.map q ≫ b
    rw [← hpj, Spec.map_comp, Category.assoc, Category.assoc, h]

variable {S : Scheme.{u}} {C B : CommRingCat.{u}}
variable (s : Spec C ⟶ S) (p : C ⟶ B)

noncomputable def reductionMap : Over.mk (Spec.map p ≫ s) ⟶ Over.mk s :=
  Over.homMk (Spec.map p) rfl

noncomputable def reduction (A : Over S) [MonObj A] :
    (Over.mk s ⟶ A) →* (Over.mk (Spec.map p ≫ s) ⟶ A) where
  toFun a := reductionMap s p ≫ a
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

theorem reduction_eq_quotient [IsLocalRing C] (hp : Function.Surjective p)
    (A : Over S) [MonObj A] (a b : Over.mk s ⟶ A) :
    reduction s p A a = reduction s p A b ↔
      LocalPowerIn.LocalPower.reduction s (RingHom.ker p.hom) A a =
        LocalPowerIn.LocalPower.reduction s (RingHom.ker p.hom) A b := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    exact (quotient_precomp_eq_iff p hp a.left b.left).mpr
      (congrArg (fun z => z.left) h)
  · intro h
    apply Over.OverMorphism.ext
    exact (quotient_precomp_eq_iff p hp a.left b.left).mp
      (congrArg (fun z => z.left) h)

theorem exists_root_in_kernel [IsLocalRing C]
    (hp : Function.Surjective p) (hker : RingHom.ker p.hom ^ 2 = ⊥)
    (A : Over S) [MonObj A] [IsCommMonObj A] (n : ℕ) (hn : IsUnit (n : C))
    (a : Over.mk s ⟶ A) (ha : reduction s p A a = 1) :
    ∃ b : Over.mk s ⟶ A, reduction s p A b = 1 ∧ b ^ n = a := by
  have ha' : reduction s p A a = reduction s p A 1 := ha.trans (map_one _).symm
  have hq : LocalPowerIn.LocalPower.reduction s (RingHom.ker p.hom) A a = 1 :=
    ((reduction_eq_quotient s p hp A a 1).mp ha').trans (map_one _)
  obtain ⟨b, hb, -⟩ := LocalPowerIn.LocalPower.exists_unique_root_in_kernel s (RingHom.ker p.hom) hker A n hn a hq
  refine ⟨b, ?_, hb.2⟩
  exact ((reduction_eq_quotient s p hp A b 1).mpr
    (hb.1.trans (map_one _).symm)).trans (map_one _)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SurjectiveReductionEq.SurjectiveReduction
