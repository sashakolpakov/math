import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues

/-! # Pairing Base Change Flip -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
The base change of the transposed scheme pairing is the transpose of
the actual base-changed pairing, with equality of the scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
    {S : Scheme.{u}} {A B W : Over S} [GrpObj A] [GrpObj B] [GrpObj W]
    (e d : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (h : ∀ (U : Over S) (x : U ⟶ A) (y : U ⟶ B), e.pairValue x y = d.pairValue x y) : e = d := by
  have hh := h (A ⊗ B) (fst A B) (snd A B)
  have hhom : e.hom = d.hom := by
    simpa only [Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] using hh
  cases e
  cases d
  cases hhom
  rfl

theorem PairingBaseChangeFlip.Construction.nativePairingPullback_flip
    {S T : Scheme.{u}} (f : T ⟶ S) (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := K.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    PairingBaseChange.Construction.nativePairingPullback f K G e.flip = (PairingBaseChange.Construction.nativePairingPullback f G K e).flip := by
  apply Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro U x y
  exact (PairingBaseChangeValues.Construction.nativePairingPullback_native_value f K G e.flip U x y).trans
    ((congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U)
      (e.flip_pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f K U).symm x)
        ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm y))).trans
          ((PairingBaseChangeValues.Construction.nativePairingPullback_native_value f G K e U y x).symm.trans
            ((PairingBaseChange.Construction.nativePairingPullback f G K e).flip_pairValue x y).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
