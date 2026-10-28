import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy

/-! # Pairing From Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
A natural bilinear family on actual scheme-valued points determines
its scheme pairing. The map is evaluated at the two universal points
of the product, so its values are proved to be the original family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B W : Over S} [GrpObj A] [GrpObj B] [GrpObj W]
  (v : ∀ (T : Over S), (T ⟶ A) → (T ⟶ B) → (T ⟶ W))
  (hnatural : ∀ {T U : Over S} (f : U ⟶ T) (x : T ⟶ A) (y : T ⟶ B),
    v U (f ≫ x) (f ≫ y) = f ≫ v T x y)

omit [GrpObj A] [GrpObj B] [GrpObj W] in
include hnatural in
theorem Annihilator.Construction.SchemeBicharacter.universalPairValue (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    lift x y ≫ v (A ⊗ B) (fst A B) (snd A B) = v T x y := by
  have h := hnatural (lift x y) (fst A B) (snd A B)
  simpa only [lift_fst, lift_snd] using h.symm

def Annihilator.Construction.SchemeBicharacter.ofPointValues
    (honeL : ∀ (T : Over S) (y : T ⟶ B), v T 1 y = 1)
    (honeR : ∀ (T : Over S) (x : T ⟶ A), v T x 1 = 1)
    (hmulL : ∀ (T : Over S) (x z : T ⟶ A) (y : T ⟶ B), v T (x * z) y = v T x y * v T z y)
    (hmulR : ∀ (T : Over S) (x : T ⟶ A) (y z : T ⟶ B), v T x (y * z) = v T x y * v T x z) :
    Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W) where
  hom := v (A ⊗ B) (fst A B) (snd A B)
  one_left T y := (Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural T 1 y).trans (honeL T y)
  one_right T x := (Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural T x 1).trans (honeR T x)
  mul_left T x z y := by
    rw [Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural, Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural, Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural]
    exact hmulL T x z y
  mul_right T x y z := by
    rw [Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural, Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural, Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural]
    exact hmulR T x y z

theorem Annihilator.Construction.SchemeBicharacter.ofPointValues_pairValue
    (honeL : ∀ (T : Over S) (y : T ⟶ B), v T 1 y = 1)
    (honeR : ∀ (T : Over S) (x : T ⟶ A), v T x 1 = 1)
    (hmulL : ∀ (T : Over S) (x z : T ⟶ A) (y : T ⟶ B), v T (x * z) y = v T x y * v T z y)
    (hmulR : ∀ (T : Over S) (x : T ⟶ A) (y z : T ⟶ B), v T x (y * z) = v T x y * v T x z)
    (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    (Annihilator.Construction.SchemeBicharacter.ofPointValues v hnatural honeL honeR hmulL hmulR).pairValue x y = v T x y :=
  Annihilator.Construction.SchemeBicharacter.universalPairValue v hnatural T x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
