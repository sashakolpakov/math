import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy

/-! # Split Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairing.Construction

noncomputable section

/-!
The split alternating pairing is an actual scheme bicharacter, with value
e(x,y') / e(x',y). Its relative annihilator agrees with the earlier
all-test-scheme split orthogonality predicate.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B W P : Over S} [GrpObj A] [GrpObj B]
  [GrpObj W] [IsCommMonObj W]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))

def splitPairValue {X : Over S} (x y : X ⟶ A ⊗ B) : X ⟶ W :=
  e.pairValue (x ≫ fst A B) (y ≫ snd A B) /
    e.pairValue (y ≫ fst A B) (x ≫ snd A B)

omit [IsCommMonObj W] in
theorem splitPairValue_natural {X Y : Over S} (f : X ⟶ Y) (x y : Y ⟶ A ⊗ B) :
    splitPairValue e (f ≫ x) (f ≫ y) = f ≫ splitPairValue e x y := by
  simp only [splitPairValue, Category.assoc, Annihilator.Construction.SchemeBicharacter.pairValue_natural,
    div_eq_mul_inv, MonObj.comp_mul, GrpObj.comp_inv]

set_option backward.isDefEq.respectTransparency false in
def splitSchemeBicharacter : Annihilator.Construction.SchemeBicharacter (A := A ⊗ B) (B := A ⊗ B) (W := W) where
  hom := splitPairValue e (fst (A ⊗ B) (A ⊗ B)) (snd (A ⊗ B) (A ⊗ B))
  one_left X y := by
    rw [← splitPairValue_natural, lift_fst, lift_snd]
    simp only [splitPairValue, MonObj.one_comp, Annihilator.Construction.SchemeBicharacter.pairValue,
      e.one_left, e.one_right, div_self']
  one_right X x := by
    rw [← splitPairValue_natural, lift_fst, lift_snd]
    simp only [splitPairValue, MonObj.one_comp, Annihilator.Construction.SchemeBicharacter.pairValue,
      e.one_left, e.one_right, div_self']
  mul_left X x z y := by
    simp only [← splitPairValue_natural, lift_fst, lift_snd]
    simp only [splitPairValue, MonObj.mul_comp, Annihilator.Construction.SchemeBicharacter.pairValue, e.mul_left, e.mul_right]
    exact (div_mul_div_comm _ _ _ _).symm
  mul_right X x y z := by
    simp only [← splitPairValue_natural, lift_fst, lift_snd]
    simp only [splitPairValue, MonObj.mul_comp, Annihilator.Construction.SchemeBicharacter.pairValue, e.mul_left, e.mul_right]
    exact (div_mul_div_comm _ _ _ _).symm

theorem splitSchemeBicharacter_pairValue {X : Over S} (x y : X ⟶ A ⊗ B) :
    (splitSchemeBicharacter e).pairValue x y = splitPairValue e x y := by
  change lift x y ≫ splitPairValue e _ _ = _
  rw [← splitPairValue_natural, lift_fst, lift_snd]

theorem splitSchemeBicharacter_alternating (X : Over S) (x : X ⟶ A ⊗ B) :
    (splitSchemeBicharacter e).pairValue x x = 1 := by
  rw [splitSchemeBicharacter_pairValue, splitPairValue, div_self']

theorem splitSchemeBicharacter_relativeAnnihilator (H : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (A ⊗ B) P) :
    (splitSchemeBicharacter e).relativeAnnihilator H = Relative.Isotropy.Construction.relativeSplitOrthogonal e H := by
  ext X t z
  change (∀ (Y : Over S) (f : Y ⟶ X) (w : Y ⟶ A ⊗ B),
    w ∈ H.points Y (f ≫ t) → (splitSchemeBicharacter e).pairValue w (f ≫ z) = 1) ↔ _
  simp only [splitSchemeBicharacter_pairValue, splitPairValue, div_eq_one, Category.assoc]
  rfl

theorem splitSchemeBicharacter_self_annihilating_of_CartierDuality (H : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (h_CartierDuality : e.flip.relativeAnnihilator (e.relativeAnnihilator H) = H) :
    (splitSchemeBicharacter e).relativeAnnihilator
        (Relative.Isotropy.Construction.pairedRelativeSubgroup H (e.relativeAnnihilator H)) =
      Relative.Isotropy.Construction.pairedRelativeSubgroup H (e.relativeAnnihilator H) := by
  rw [splitSchemeBicharacter_relativeAnnihilator]
  exact Relative.Isotropy.Construction.relative_maximal_isotropic_of_CartierDuality e H h_CartierDuality

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairing.Construction
