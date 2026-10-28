import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingAdjoints

/-! # Annihilator Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
The character defining a sheaf annihilator is trivial exactly when the
original scheme pairing vanishes after every test-scheme restriction.
Thus the sheaf kernel uses the same all-test annihilation condition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_rightAdjoint :
    e.toSheafPairing.rightAdjoint = e.flip.toSheafPairing.leftAdjoint :=
  (congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint e.toSheafPairing_flip).symm

def Annihilator.Construction.SchemeBicharacter.rightRestrictionCharacter (i : H ⟶ A) [IsMonHom i] (T : Over S) (y : T ⟶ B) :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk H))).obj.obj (.op T) :=
  ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk i)).op).hom.app (.op T)
    (e.toSheafPairing.rightAdjoint.hom.app (.op T) (ULift.up y))

theorem Annihilator.Construction.SchemeBicharacter.rightRestrictionCharacter_value (i : H ⟶ A) [IsMonHom i]
    (T : Over S) (y : T ⟶ B) (U : Over T) (x : U.left ⟶ H) :
    (e.rightRestrictionCharacter i T y).app (.op U) (ULift.up x) =
      ULift.up (e.pairValue (x ≫ i) (U.hom ≫ y)) := by
  unfold Annihilator.Construction.SchemeBicharacter.rightRestrictionCharacter
  rw [Annihilator.Construction.SchemeBicharacter.toSheafPairing_rightAdjoint]
  change ULift.up (e.flip.pairValue (U.hom ≫ y) (x ≫ i)) = _
  exact congrArg ULift.up (e.flip_pairValue _ _)

theorem Annihilator.Construction.SchemeBicharacter.rightRestrictionCharacter_eq_one_iff (i : H ⟶ A) [IsMonHom i]
    (T : Over S) (y : T ⟶ B) :
    e.rightRestrictionCharacter i T y = 1 ↔
      ∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ H), e.pairValue (x ≫ i) (f ≫ y) = 1 := by
  constructor
  · intro h U f x
    have hv := congrArg (fun χ => χ.app (.op (Over.mk f)) (ULift.up x)) h
    rw [Annihilator.Construction.SchemeBicharacter.rightRestrictionCharacter_value] at hv
    exact congrArg ULift.down hv
  · intro h
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨x⟩
    exact (e.rightRestrictionCharacter_value i T y U.unop x).trans
      (congrArg ULift.up (h U.unop.left U.unop.hom x))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
