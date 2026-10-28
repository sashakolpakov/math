import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power

/-! # End Torsion Free -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.EndTorsionFree

noncomputable section

/-! Integral endomorphisms of a connected proper group in characteristic
zero have no additive torsion. The proof uses actual unramified power maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [CharZero k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [ConnectedSpace A.left]

omit [CharZero k] [IsProper A.hom] [ConnectedSpace A.left] in
theorem endSchemeMap_nsmul (n : ℕ) (a : End.IntegralEnd A) :
    End.endSchemeMap A (n • a) = End.endSchemeMap A a ^ n := by
  induction n with
  | zero => rw [zero_smul, BaseChange.endSchemeMap_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, BaseChange.endSchemeMap_add, ih, pow_succ]

omit [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [ConnectedSpace A.left] in
theorem nonzero_nat_unit_on_field_base (n : ℕ) (hn : n ≠ 0) :
    ∀ x : Spec (.of k), IsUnit (n : (Spec (.of k)).presheaf.stalk x) := by
  intro x
  have hu : IsUnit (n : k) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  let r : k →+* (Spec (.of k)).presheaf.stalk x :=
    ((Spec (.of k)).presheaf.germ ⊤ x (by trivial)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using hu.map r

theorem integralEnd_eq_zero_of_nsmul (n : ℕ) (hn : n ≠ 0) (a : End.IntegralEnd A)
    (ha : n • a = 0) : a = 0 := by
  let p := (𝟙 A : A ⟶ A) ^ n
  have : IsProper p.left := TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  have : FormallyUnramified p.left := TorsionQuotient.Power.PowerGeometry.power_formallyUnramified A n
    (nonzero_nat_unit_on_field_base (k := k) n hn)
  have hp : End.endSchemeMap A a ^ n = 1 := by
    have h := congrArg (End.endSchemeMap A) ha
    rw [endSchemeMap_nsmul, BaseChange.endSchemeMap_zero] at h
    exact h
  have hc : (End.endSchemeMap A a).left ≫ p.left = (1 : A ⟶ A).left ≫ p.left := by
    change (End.endSchemeMap A a ≫ p).left = ((1 : A ⟶ A) ≫ p).left
    apply congrArg Over.Hom.left
    change End.endSchemeMap A a ≫ (𝟙 A : A ⟶ A) ^ n = (1 : A ⟶ A) ≫ (𝟙 A : A ⟶ A) ^ n
    rw [MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, hp, one_pow]
  have hpoint : (MonObj.one (X := A)).left ≫ (End.endSchemeMap A a).left =
      (MonObj.one (X := A)).left ≫ (1 : A ⟶ A).left := by
    change (MonObj.one (X := A) ≫ End.endSchemeMap A a).left =
      (MonObj.one (X := A) ≫ (1 : A ⟶ A)).left
    apply congrArg Over.Hom.left
    simp only [MonObj.one_eq_one, MonObj.one_comp, MonObj.comp_one]
  apply End.endSchemeMap_injective A
  rw [BaseChange.endSchemeMap_zero]
  apply Over.OverMorphism.ext
  have : Nonempty (CategoryTheory.MonoidalCategory.tensorUnit (Over (Spec (.of k)))).left :=
    ⟨IsLocalRing.closedPoint k⟩
  exact PELModuli.IntegralModel.PointedLifts.pointed_unramified_lifts_unique p.left (End.endSchemeMap A a).left
    (1 : A ⟶ A).left hc (MonObj.one (X := A)).left hpoint

theorem integralEnd_isAddTorsionFree : IsAddTorsionFree (End.IntegralEnd A) := by
  refine ⟨fun n hn a b hab => ?_⟩
  apply sub_eq_zero.mp
  apply integralEnd_eq_zero_of_nsmul A n hn
  change n • a = n • b at hab
  rw [nsmul_sub, hab, sub_self]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.EndTorsionFree
