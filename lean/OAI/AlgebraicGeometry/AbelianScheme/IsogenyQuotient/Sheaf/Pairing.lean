import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingFromPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SheafPairing

/-! # Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing.Construction

noncomputable section

/-!
Reconstruct the actual scheme map from a bilinear pairing of represented
fppf sheaves. Both comparison directions preserve every test-scheme value;
the sheaf interface does not introduce a separate geometric pairing choice.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)))

def sheafPairingNativeValue (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X :=
  (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) T
    (e.leftAdjoint.hom.app (.op T) (ULift.up x)) (ULift.up y)).down

theorem sheafPairingNativeValue_right (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    sheafPairingNativeValue e T x y =
      (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) T
        (e.rightAdjoint.hom.app (.op T) (ULift.up y)) (ULift.up x)).down :=
  congrArg ULift.down (e.adjoint_value T (ULift.up x) (ULift.up y)).symm

theorem sheafPairingNativeValue_natural {T U : Over S} (f : U ⟶ T) (x : T ⟶ A) (y : T ⟶ B) :
    sheafPairingNativeValue e U (f ≫ x) (f ≫ y) = f ≫ sheafPairingNativeValue e T x y := by
  have hn := e.leftAdjoint.hom.naturality_apply f.op (ULift.up x)
  have hv := CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue_natural (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) f
    (e.leftAdjoint.hom.app (.op T) (ULift.up x)) (ULift.up y)
  change e.leftAdjoint.hom.app (.op U) (ULift.up (f ≫ x)) =
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B))).obj.map f.op
      (e.leftAdjoint.hom.app (.op T) (ULift.up x)) at hn
  unfold sheafPairingNativeValue
  rw [hn]
  exact congrArg ULift.down hv

def sheafPairingToScheme :
    Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Annihilator.Construction.SchemeBicharacter.ofPointValues (sheafPairingNativeValue e) (sheafPairingNativeValue_natural e)
    (by
      intro T y
      rw [sheafPairingNativeValue_right]
      exact congrArg ULift.down
        (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) T
          (e.rightAdjoint.hom.app (.op T) (ULift.up y))).map_one)
    (by
      intro T x
      exact congrArg ULift.down
        (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) T
          (e.leftAdjoint.hom.app (.op T) (ULift.up x))).map_one)
    (by
      intro T x z y
      rw [sheafPairingNativeValue_right, sheafPairingNativeValue_right, sheafPairingNativeValue_right]
      exact congrArg ULift.down
        ((CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) T
          (e.rightAdjoint.hom.app (.op T) (ULift.up y))).map_mul (ULift.up x) (ULift.up z)))
    (by
      intro T x y z
      exact congrArg ULift.down
        ((CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) T
          (e.leftAdjoint.hom.app (.op T) (ULift.up x))).map_mul (ULift.up y) (ULift.up z)))

theorem sheafPairingToScheme_value (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    (sheafPairingToScheme e).pairValue x y = sheafPairingNativeValue e T x y :=
  Annihilator.Construction.SchemeBicharacter.ofPointValues_pairValue _ _ _ _ _ _ T x y

theorem sheafPairingToScheme_toSheaf : (sheafPairingToScheme e).toSheafPairing = e := by
  have h : (sheafPairingToScheme e).toSheafPairing.leftAdjoint = e.leftAdjoint := by
    apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
    intro T x y
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    change T ⟶ A at x
    change T ⟶ B at y
    exact ((sheafPairingToScheme e).toSheafPairing_value T x y).trans
      (congrArg ULift.up (sheafPairingToScheme_value e T x y))
  exact congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk h

theorem schemePairingToSheaf_toScheme
    (b : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    sheafPairingToScheme b.toSheafPairing = b := by
  have h : (sheafPairingToScheme b.toSheafPairing).hom = b.hom :=
    (sheafPairingToScheme b.toSheafPairing).toSheafPairing_hom_injective b
      (sheafPairingToScheme_toSheaf b.toSheafPairing)
  have hext : ∀ c d : Annihilator.Construction.SchemeBicharacter (A := A) (B := B)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X), c.hom = d.hom → c = d := by
    rintro ⟨c, _, _, _, _⟩ ⟨d, _, _, _, _⟩ hcd
    cases hcd
    rfl
  exact hext _ _ h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing.Construction
