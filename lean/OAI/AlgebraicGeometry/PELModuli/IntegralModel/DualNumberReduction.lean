import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.GroupTangentsEq

/-! # Dual Number Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualNumberReduction

noncomputable section

/-! The actual dual-number reduction agrees with the quotient by its
square-zero kernel, on scheme maps in every characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AlgebraicLie

variable (k : Type) [Field k]

abbrev dualBase : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

instance dualNumber_isLocalRing : IsLocalRing (DualNumber k) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

def dualIdeal : Ideal (DualNumber k) := RingHom.ker (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)

theorem dualIdeal_square : dualIdeal k ^ 2 = ⊥ := by
  apply le_antisymm
  · rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change x * y = 0
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    apply TrivSqZeroExt.ext
    · change x.fst * y.fst = 0
      rw [hx, zero_mul]
    · rw [DualNumber.snd_mul, hx, hy, zero_mul, mul_zero, add_zero]
      rfl
  · exact bot_le

def quotientSection : k →+* (DualNumber k ⧸ dualIdeal k) :=
  (Ideal.Quotient.mk (dualIdeal k)).comp (algebraMap k (DualNumber k))

theorem quotientSection_comp_reduction :
    (quotientSection k).comp (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k) = Ideal.Quotient.mk (dualIdeal k) := by
  apply RingHom.ext
  intro x
  apply Ideal.Quotient.eq.mpr
  change ((algebraMap k (DualNumber k) x.fst) - x).fst = 0
  change x.fst - x.fst = 0
  exact sub_self _

def quotientReduction : (DualNumber k ⧸ dualIdeal k) →+* k :=
  Ideal.Quotient.lift (dualIdeal k) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k) (fun _ h => h)

theorem quotientReduction_comp :
    (quotientReduction k).comp (Ideal.Quotient.mk (dualIdeal k)) = AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k := by
  apply RingHom.ext
  intro x
  rfl

theorem quotient_reduction_eq_iff {X : Scheme.{0}}
    (f h : Spec (.of (DualNumber k)) ⟶ X) :
    Spec.map (CommRingCat.ofHom (R := DualNumber k) (S := DualNumber k ⧸ dualIdeal k) (Ideal.Quotient.mk (dualIdeal k))) ≫ f =
        Spec.map (CommRingCat.ofHom (R := DualNumber k) (S := DualNumber k ⧸ dualIdeal k) (Ideal.Quotient.mk (dualIdeal k))) ≫ h ↔
      Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) ≫ f =
        Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) ≫ h := by
  constructor
  · intro e
    have hr : Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) =
        Spec.map (CommRingCat.ofHom (quotientReduction k)) ≫
          Spec.map (CommRingCat.ofHom (R := DualNumber k) (S := DualNumber k ⧸ dualIdeal k) (Ideal.Quotient.mk (dualIdeal k))) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom (quotientReduction_comp k).symm)
    rw [hr, Category.assoc, Category.assoc, e]
  · intro e
    have hr : Spec.map (CommRingCat.ofHom (R := DualNumber k) (S := DualNumber k ⧸ dualIdeal k) (Ideal.Quotient.mk (dualIdeal k))) =
        Spec.map (CommRingCat.ofHom (quotientSection k)) ≫
          Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom (quotientSection_comp_reduction k).symm)
    rw [hr, Category.assoc, Category.assoc, e]

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualNumberReduction
