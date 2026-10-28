import OAI.RepresentationTheory.Theta.Geometric.DualNumbers
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero
import Mathlib.RingTheory.DualNumber

/-! # Number Lifts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.NumberLifts

noncomputable section

/-! Geometric point derivations give the intrinsic square-zero lift module
used for group-scheme tangent addition. -/

section Ideal

variable (F : Type) [Field F]

def dualNumberIdeal : Ideal (DualNumber F) :=
  RingHom.ker (TrivSqZeroExt.fstHom F F F).toRingHom

theorem dualNumberIdeal_mem (a : DualNumber F) : a ∈ dualNumberIdeal F ↔ a.fst = 0 := Iff.rfl

theorem dualNumberIdeal_square : dualNumberIdeal F ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change a * b = 0
  apply TrivSqZeroExt.ext
  · change a.fst * b.fst = 0
    rw [(dualNumberIdeal_mem F a).mp ha, zero_mul]
  · change a.fst * b.snd + a.snd * b.fst = 0
    rw [(dualNumberIdeal_mem F a).mp ha, (dualNumberIdeal_mem F b).mp hb]
    simp

end Ideal

variable {k A F : Type} [Field k] [CommRing A] [Field F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

def constantDualNumberPoint : A →+* DualNumber F :=
  (algebraMap F (DualNumber F)).comp (algebraMap A F)

def geometricDerivationLift (δ : Derivation k A F) :
    AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (dualNumberIdeal F) (dualNumberIdeal_square F)
      (constantDualNumberPoint (A := A)) where
  hom := (DualNumbers.geometricDerivationJet δ).toRingHom
  congruent a := by
    rw [dualNumberIdeal_mem]
    change (DualNumbers.geometricDerivationJet δ a).fst -
      (algebraMap F (DualNumber F) (algebraMap A F a)).fst = 0
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem geometricDerivationLift_add (δ ε : Derivation k A F) :
    geometricDerivationLift (δ + ε) = geometricDerivationLift δ + geometricDerivationLift ε := by
  apply AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
  apply RingHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · change algebraMap A F a =
      algebraMap A F a + algebraMap A F a -
        (algebraMap F (DualNumber F) (algebraMap A F a)).fst
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · change δ a + ε a = δ a + ε a -
      (algebraMap F (DualNumber F) (algebraMap A F a)).snd
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem geometricDerivationLift_smul (c : F) (δ : Derivation k A F) :
    geometricDerivationLift (c • δ) =
      algebraMap F (DualNumber F) c • geometricDerivationLift δ := by
  apply AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
  apply RingHom.ext
  intro a
  change DualNumbers.geometricDerivationJet (c • δ) a =
    algebraMap F (DualNumber F) (algebraMap A F a) + algebraMap F (DualNumber F) c *
      (DualNumbers.geometricDerivationJet δ a - algebraMap F (DualNumber F) (algebraMap A F a))
  apply TrivSqZeroExt.ext <;>
    simp [TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.NumberLifts
