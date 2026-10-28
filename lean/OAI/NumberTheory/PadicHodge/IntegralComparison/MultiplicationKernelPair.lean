import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Left

/-! # Multiplication Kernel Pair -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationKernelPair

noncomputable section

/-! The overlap of the actual multiplication cover is the product of
the original group scheme with its multiplication kernel. These explicit
coordinates identify overlap differences with torsion translations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)

local notation "m" => ((𝟙 A : A ⟶ A) ^ n)
local notation "T" => OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n
local notation "P" => pullback m m

theorem difference_torsion :
    ((pullback.snd m m : P ⟶ A) / pullback.fst m m) ^ n = 1 := by
  have h : (pullback.snd m m : P ⟶ A) ^ n = (pullback.fst m m) ^ n := by
    simpa only [MonObj.comp_pow, Category.comp_id] using
      (pullback.condition (f := m) (g := m)).symm
  rw [div_pow, h, div_self']

def difference : P ⟶ T :=
  AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n ((pullback.snd m m : P ⟶ A) / pullback.fst m m)
    (difference_torsion A n)

@[reassoc (attr := simp)] theorem difference_inclusion :
    difference A n ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n =
      (pullback.snd m m : P ⟶ A) / pullback.fst m m :=
  AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

theorem translation_condition :
    (fst A T : A ⊗ T ⟶ A) ≫ m =
      ((fst A T) * (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)) ≫ m := by
  have ht : (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) ^ n = 1 :=
    (AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
      ⟨snd A T, rfl⟩
  simp only [MonObj.comp_pow, Category.comp_id, mul_pow, ht, _root_.mul_one]

def toPair : A ⊗ T ⟶ P :=
  pullback.lift (fst A T) ((fst A T) * (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n))
    (translation_condition A n)

def fromPair : P ⟶ A ⊗ T := lift (pullback.fst m m) (difference A n)

@[reassoc (attr := simp)] theorem toPair_fst : toPair A n ≫ pullback.fst m m = fst A T :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem toPair_snd : toPair A n ≫ pullback.snd m m =
    (fst A T) * (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem fromPair_fst : fromPair A n ≫ fst A T = pullback.fst m m :=
  lift_fst _ _

@[reassoc (attr := simp)] theorem fromPair_snd : fromPair A n ≫ snd A T = difference A n :=
  lift_snd _ _

def equiv : A ⊗ T ≅ P where
  hom := toPair A n
  inv := fromPair A n
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, fromPair_fst, toPair_fst, Category.id_comp]
    · apply equalizer.hom_ext
      change (toPair A n ≫ fromPair A n) ≫ snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n =
        (𝟙 (A ⊗ T)) ≫ snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n
      simp only [Category.assoc, fromPair_snd_assoc, difference_inclusion,
        GrpObj.comp_div, toPair_fst, toPair_snd, Category.id_comp]
      exact mul_div_cancel_left _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, toPair_fst, fromPair_fst, Category.id_comp]
    · simp only [Category.assoc, toPair_snd, MonObj.comp_mul, fromPair_fst,
        fromPair_snd_assoc, difference_inclusion, Category.id_comp]
      exact mul_div_cancel _ _

def schemeEquiv : (A ⊗ T).left ≅
    pullback (((𝟙 A : A ⟶ A) ^ n).left) (((𝟙 A : A ⟶ A) ^ n).left) :=
  (Over.forget S).mapIso (equiv A n) ≪≫
    ((IsPullback.of_hasPullback m m).map (Over.forget S)).isoPullback

@[reassoc (attr := simp)] theorem schemeEquiv_hom_fst :
    (schemeEquiv A n).hom ≫
      pullback.fst (((𝟙 A : A ⟶ A) ^ n).left) (((𝟙 A : A ⟶ A) ^ n).left) =
        (fst A T).left := by
  let F := Over.forget S
  let h := (IsPullback.of_hasPullback m m).map F
  change (F.map (toPair A n) ≫ h.isoPullback.hom) ≫ pullback.fst (F.map m) (F.map m) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => F.map (toPair A n) ≫ t) h.isoPullback_hom_fst).trans
      ((F.map_comp _ _).symm.trans (congrArg F.map (toPair_fst A n))))

@[reassoc (attr := simp)] theorem schemeEquiv_hom_snd :
    (schemeEquiv A n).hom ≫
      pullback.snd (((𝟙 A : A ⟶ A) ^ n).left) (((𝟙 A : A ⟶ A) ^ n).left) =
        ((fst A T) * (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).left := by
  let F := Over.forget S
  let h := (IsPullback.of_hasPullback m m).map F
  change (F.map (toPair A n) ≫ h.isoPullback.hom) ≫ pullback.snd (F.map m) (F.map m) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => F.map (toPair A n) ≫ t) h.isoPullback_hom_snd).trans
      ((F.map_comp _ _).symm.trans (congrArg F.map (toPair_snd A n))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationKernelPair
