import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteCoverCocycles
import Mathlib.RingTheory.Localization.BaseChange

/-! # Principal Overlaps -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalOverlaps.Construction

noncomputable section

/-! Tensor coordinates for intersections of principal affine opens. -/

open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

theorem isLocalization_principalTensor (f g : R) :
    IsLocalization.Away (f * g) (Localization.Away f ⊗[R] Localization.Away g) := by
  let : IsLocalization.Away (algebraMap R (Localization.Away f) g)
      (Localization.Away f ⊗[R] Localization.Away g) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (IsLocalization.tensor (S := Localization.Away f)
        (Localization.Away g) (Submonoid.powers g))
  exact IsLocalization.Away.mul' (Localization.Away f)
    (Localization.Away f ⊗[R] Localization.Away g) f g

def principalOverlapAlgEquiv (f g : R) :
    (Localization.Away f ⊗[R] Localization.Away g) ≃ₐ[R] Localization.Away (f * g) := by
  let := isLocalization_principalTensor R f g
  exact IsLocalization.algEquiv (Submonoid.powers (f * g)) _ _

def principalOverlapModuleEquiv (f g : R) (M : Type v) [AddCommGroup M] [Module R M] :
    Localization.Away f ⊗[R] (Localization.Away g ⊗[R] M) ≃ₗ[R]
      Localization.Away (f * g) ⊗[R] M :=
  (TensorProduct.assoc R _ _ _).symm ≪≫ₗ
    (principalOverlapAlgEquiv R f g).toLinearEquiv.rTensor M

def principalRestriction (f h : R) (hfh : f ∣ h) :
    Localization.Away f →ₐ[R] Localization.Away h where
  __ := IsLocalization.Away.lift f
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away h) h hfh)
  commutes' r := IsLocalization.Away.lift_eq _ _ r

theorem principalRestriction_algebraMap (f h : R) (hfh : f ∣ h) (r : R) :
    principalRestriction R f h hfh (algebraMap R _ r) = algebraMap R _ r :=
  (principalRestriction R f h hfh).commutes r

theorem principalRestriction_comp (f g h : R) (hfg : f ∣ g) (hgh : g ∣ h) :
    (principalRestriction R g h hgh).comp (principalRestriction R f g hfg) =
      principalRestriction R f h (hfg.trans hgh) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  exact Subsingleton.elim _ _

theorem principalRestriction_comp_apply (f g h : R) (hfg : f ∣ g) (hgh : g ∣ h)
    (a : Localization.Away f) :
    principalRestriction R g h hgh (principalRestriction R f g hfg a) =
      principalRestriction R f h (hfg.trans hgh) a :=
  AlgHom.congr_fun (principalRestriction_comp R f g h hfg hgh) a

theorem principalOverlapAlgEquiv_includeLeft (f g : R) :
    (principalOverlapAlgEquiv R f g).toAlgHom.comp Algebra.TensorProduct.includeLeft =
      principalRestriction R f (f * g) (dvd_mul_right f g) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  exact Subsingleton.elim _ _

theorem principalOverlapAlgEquiv_includeRight (f g : R) :
    (principalOverlapAlgEquiv R f g).toAlgHom.comp Algebra.TensorProduct.includeRight =
      principalRestriction R g (f * g) (dvd_mul_left g f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  exact Subsingleton.elim _ _

theorem principalOverlapAlgEquiv_tmul (f g : R) (a : Localization.Away f)
    (b : Localization.Away g) :
    principalOverlapAlgEquiv R f g (a ⊗ₜ[R] b) =
      principalRestriction R f (f * g) (dvd_mul_right f g) a *
        principalRestriction R g (f * g) (dvd_mul_left g f) b := by
  have ha := AlgHom.congr_fun (principalOverlapAlgEquiv_includeLeft R f g) a
  have hb := AlgHom.congr_fun (principalOverlapAlgEquiv_includeRight R f g) b
  change principalOverlapAlgEquiv R f g (a ⊗ₜ[R] 1) = _ at ha
  change principalOverlapAlgEquiv R f g (1 ⊗ₜ[R] b) = _ at hb
  rw [← ha, ← hb, ← map_mul]
  simp

variable (M : Type v) [AddCommGroup M] [Module R M]

def principalRestrictionModule (f h : R) (hfh : f ∣ h) :
    Localization.Away f ⊗[R] M →ₗ[R] Localization.Away h ⊗[R] M :=
  (principalRestriction R f h hfh).toLinearMap.rTensor M

theorem principalOverlapModuleEquiv_tmul (f g : R) (a : Localization.Away f)
    (b : Localization.Away g) (m : M) :
    principalOverlapModuleEquiv R f g M (a ⊗ₜ[R] (b ⊗ₜ[R] m)) =
      (principalRestriction R f (f * g) (dvd_mul_right f g) a *
        principalRestriction R g (f * g) (dvd_mul_left g f) b) ⊗ₜ[R] m := by
  simp [principalOverlapModuleEquiv, principalOverlapAlgEquiv_tmul]

theorem principalOverlapModuleEquiv_insert_left (f g : R) (z : Localization.Away g ⊗[R] M) :
    principalOverlapModuleEquiv R f g M (1 ⊗ₜ[R] z) =
      principalRestrictionModule R M g (f * g) (dvd_mul_left g f) z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m => simp [principalOverlapModuleEquiv_tmul, principalRestrictionModule]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem principalOverlapModuleEquiv_insert_right (f g : R) (z : Localization.Away f ⊗[R] M) :
    principalOverlapModuleEquiv R f g M ((TensorProduct.mk R (Localization.Away g) M 1).lTensor
      (Localization.Away f) z) =
      principalRestrictionModule R M f (f * g) (dvd_mul_right f g) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a m => simp [principalOverlapModuleEquiv_tmul, principalRestrictionModule]
  | add x y hx hy => simp [hx, hy]

def principalTripleModuleEquiv (f g h : R) :
    Localization.Away f ⊗[R] (Localization.Away g ⊗[R] (Localization.Away h ⊗[R] M)) ≃ₗ[R]
      Localization.Away (f * (g * h)) ⊗[R] M :=
  (principalOverlapModuleEquiv R g h M).lTensor (Localization.Away f) ≪≫ₗ
    principalOverlapModuleEquiv R f (g * h) M

theorem principalTripleModuleEquiv_tmul (f g h : R) (a : Localization.Away f)
    (b : Localization.Away g) (c : Localization.Away h) (m : M) :
    principalTripleModuleEquiv R M f g h (a ⊗ₜ[R] (b ⊗ₜ[R] (c ⊗ₜ[R] m))) =
      (principalRestriction R f (f * (g * h)) (dvd_mul_right _ _) a *
        (principalRestriction R g (f * (g * h))
          ((dvd_mul_right g h).trans (dvd_mul_left (g * h) f)) b *
        principalRestriction R h (f * (g * h))
          ((dvd_mul_left h g).trans (dvd_mul_left (g * h) f)) c)) ⊗ₜ[R] m := by
  simp [principalTripleModuleEquiv, principalOverlapModuleEquiv_tmul,
    principalRestriction_comp_apply]

theorem principalTripleModuleEquiv_insert_first (f g h : R)
    (z : Localization.Away g ⊗[R] (Localization.Away h ⊗[R] M)) :
    principalTripleModuleEquiv R M f g h (1 ⊗ₜ[R] z) =
      principalRestrictionModule R M (g * h) (f * (g * h)) (dvd_mul_left _ _)
        (principalOverlapModuleEquiv R g h M z) := by
  simp [principalTripleModuleEquiv, principalOverlapModuleEquiv_insert_left]

theorem principalTripleModuleEquiv_insert_middle (f g h : R)
    (z : Localization.Away f ⊗[R] (Localization.Away h ⊗[R] M)) :
    principalTripleModuleEquiv R M f g h
      ((TensorProduct.mk R (Localization.Away g) (Localization.Away h ⊗[R] M) 1).lTensor
        (Localization.Away f) z) =
      principalRestrictionModule R M (f * h) (f * (g * h))
        (by use g; ring)
        (principalOverlapModuleEquiv R f h M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      simp [principalTripleModuleEquiv_tmul, principalOverlapModuleEquiv_tmul,
        principalRestrictionModule, principalRestriction_comp_apply]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

theorem principalTripleModuleEquiv_insert_last (f g h : R)
    (z : Localization.Away f ⊗[R] (Localization.Away g ⊗[R] M)) :
    principalTripleModuleEquiv R M f g h
      (((TensorProduct.mk R (Localization.Away h) M 1).lTensor (Localization.Away g)).lTensor
        (Localization.Away f) z) =
      principalRestrictionModule R M (f * g) (f * (g * h))
        (by use h; ring)
        (principalOverlapModuleEquiv R f g M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      simp [principalTripleModuleEquiv_tmul, principalOverlapModuleEquiv_tmul,
        principalRestrictionModule, principalRestriction_comp_apply]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalOverlaps.Construction
