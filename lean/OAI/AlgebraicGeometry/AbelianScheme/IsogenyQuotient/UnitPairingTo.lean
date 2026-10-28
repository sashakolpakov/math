import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingFromPoints

/-! # Unit Pairing To -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitPairingTo.Construction

noncomputable section

/-! Reconstruct a native pairing from its actual regular-unit values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (b : ∀ T : Over S, (T ⟶ A) →* (T ⟶ B) →* Γ(T.left, ⊤)ˣ)
  (hnatural : ∀ {T U : Over S} (f : U ⟶ T) (x : T ⟶ A) (y : T ⟶ B),
    b U (f ≫ x) (f ≫ y) = Units.map f.left.appTop.hom (b T x y))

def unitPairingToScheme :
    Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Annihilator.Construction.SchemeBicharacter.ofPointValues
    (fun T x y => (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv T).symm (b T x y))
    (by
      intro T U f x y
      rw [hnatural]
      exact MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv_symm_natural f (b T x y))
    (by intro T y; simp only [map_one, MonoidHom.one_apply])
    (by intro T x; simp only [map_one])
    (by intro T x z y; simp only [map_mul, MonoidHom.mul_apply])
    (by intro T x y z; simp only [map_mul])

theorem unitPairingToScheme_value (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    (unitPairingToScheme b hnatural).pairValue x y = (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv T).symm (b T x y) :=
  Annihilator.Construction.SchemeBicharacter.universalPairValue
    (fun U x y => (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv U).symm (b U x y))
    (by
      intro U V f a c
      rw [hnatural]
      exact MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv_symm_natural f (b U a c)) T x y

theorem unitPairingToScheme_unitValue (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T ((unitPairingToScheme b hnatural).pairValue x y) = b T x y := by
  rw [unitPairingToScheme_value]
  exact (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv T).apply_symm_apply _

theorem unitPairingToScheme_value_eq_one_iff (T : Over S) (x : T ⟶ A) (y : T ⟶ B) :
    (unitPairingToScheme b hnatural).pairValue x y = 1 ↔ b T x y = 1 := by
  rw [← unitPairingToScheme_unitValue b hnatural T x y]
  exact (map_eq_one_iff (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv T) (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv T).injective).symm

theorem unitPairingToScheme_unique
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (h : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B),
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (e.pairValue x y) = b T x y) :
    e = unitPairingToScheme b hnatural := by
  have hhom : e.hom = (unitPairingToScheme b hnatural).hom := by
    apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective (A ⊗ B)
    have he := h (A ⊗ B) (fst A B) (snd A B)
    have hb := unitPairingToScheme_unitValue b hnatural (A ⊗ B) (fst A B) (snd A B)
    simpa only [Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] using he.trans hb.symm
  have hext : ∀ c d : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X),
      c.hom = d.hom → c = d := by
    rintro ⟨c, _, _, _, _⟩ ⟨d, _, _, _, _⟩ hcd
    cases hcd
    rfl
  exact hext _ _ hhom

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitPairingTo.Construction
