import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafCharacterComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTranspose

/-! # Sheaf Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
An actual G_m-valued scheme bicharacter defines its adjoint in CartierDuality's
commutative fppf-sheaf category. The comparison retains the original
pairing values on every test scheme and every further restriction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

def Annihilator.Construction.SchemeBicharacter.sheafCharacterAt (T : Over S) (x : T ⟶ A) :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B))).obj.obj (.op T) where
  app U := GrpCat.ofHom {
    toFun y := ULift.up (e.pairValue (U.unop.hom ≫ x) y.down)
    map_one' := congrArg ULift.up (e.one_right U.unop.left (U.unop.hom ≫ x))
    map_mul' y z := congrArg ULift.up (e.mul_right U.unop.left (U.unop.hom ≫ x) y.down z.down) }
  naturality := by
    intro U V f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨y⟩
    change U.unop.left ⟶ B at y
    change ULift.up (e.pairValue (V.unop.hom ≫ x) (f.unop.left ≫ y)) =
      ULift.up (f.unop.left ≫ e.pairValue (U.unop.hom ≫ x) y)
    apply congrArg ULift.up
    rw [← e.pairValue_natural, ← Category.assoc, f.unop.w]

theorem Annihilator.Construction.SchemeBicharacter.sheafCharacterAt_one (T : Over S) : e.sheafCharacterAt T 1 = 1 := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨y⟩
  change ULift.up (e.pairValue (U.unop.hom ≫ 1) y) = ULift.up 1
  rw [MonObj.comp_one]
  exact congrArg ULift.up (e.one_left U.unop.left y)

omit [IsCommMonObj A] in
theorem Annihilator.Construction.SchemeBicharacter.sheafCharacterAt_mul (T : Over S) (x z : T ⟶ A) :
    e.sheafCharacterAt T (x * z) = e.sheafCharacterAt T x * e.sheafCharacterAt T z := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨y⟩
  change ULift.up (e.pairValue (U.unop.hom ≫ (x * z)) y) =
    ULift.up (e.pairValue (U.unop.hom ≫ x) y * e.pairValue (U.unop.hom ≫ z) y)
  rw [MonObj.comp_mul]
  exact congrArg ULift.up (e.mul_left U.unop.left (U.unop.hom ≫ x) (U.unop.hom ≫ z) y)

omit [IsCommMonObj A] in
theorem Annihilator.Construction.SchemeBicharacter.sheafCharacterAt_natural {T U : Over S} (f : U ⟶ T) (x : T ⟶ A) :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B))).obj.map f.op (e.sheafCharacterAt T x) =
      e.sheafCharacterAt U (f ≫ x) := by
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨y⟩
  change ULift.up (e.pairValue ((V.unop.hom ≫ f) ≫ x) y) =
    ULift.up (e.pairValue (V.unop.hom ≫ f ≫ x) y)
  rw [Category.assoc]

def Annihilator.Construction.SchemeBicharacter.toSheafPairing : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A))
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) where
  leftAdjoint.hom.app T := CommGrpCat.ofHom {
    toFun x := e.sheafCharacterAt T.unop x.down
    map_one' := e.sheafCharacterAt_one T.unop
    map_mul' x y := e.sheafCharacterAt_mul T.unop x.down y.down }
  leftAdjoint.hom.naturality := by
    intro T U f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨x⟩
    exact (e.sheafCharacterAt_natural f.unop x).symm

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_value (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) T
      (e.toSheafPairing.leftAdjoint.hom.app (.op T) (ULift.up x)) (ULift.up y) =
        ULift.up (e.pairValue x y) := by
  change ULift.up (e.pairValue ((𝟙 T) ≫ x) y) = _
  rw [Category.id_comp]

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_rightValue (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) T
      (e.toSheafPairing.rightAdjoint.hom.app (.op T) (ULift.up y)) (ULift.up x) =
        ULift.up (e.pairValue x y) :=
  (e.toSheafPairing.adjoint_value T (ULift.up x) (ULift.up y)).trans (e.toSheafPairing_value T x y)

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_flip : e.flip.toSheafPairing = e.toSheafPairing.flip := by
  have h : e.flip.toSheafPairing.leftAdjoint = e.toSheafPairing.rightAdjoint := by
    apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
    intro T y x
    obtain ⟨y⟩ := y
    obtain ⟨x⟩ := x
    exact (e.flip.toSheafPairing_value T y x).trans
      ((congrArg ULift.up (e.flip_pairValue y x)).trans (e.toSheafPairing_rightValue T x y).symm)
  exact congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk h

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_hom_injective
    (d : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (h : e.toSheafPairing = d.toSheafPairing) : e.hom = d.hom := by
  have hv := congrArg (fun b : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A))
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) =>
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) (A ⊗ B)
      (b.leftAdjoint.hom.app (.op (A ⊗ B)) (ULift.up (fst A B))) (ULift.up (snd A B))) h
  rw [Annihilator.Construction.SchemeBicharacter.toSheafPairing_value, Annihilator.Construction.SchemeBicharacter.toSheafPairing_value] at hv
  have hh := congrArg ULift.down hv
  simpa only [Annihilator.Construction.SchemeBicharacter.pairValue, CategoryTheory.CartesianMonoidalCategory.lift_fst_snd, Category.id_comp] using hh

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
