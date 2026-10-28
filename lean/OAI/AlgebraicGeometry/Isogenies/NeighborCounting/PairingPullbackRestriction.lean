import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks

/-! # Pairing Pullback Restriction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PairingPullbackRestriction

noncomputable section

/-! Restriction to the original chosen blocks commutes with actual
base change of scheme pairings, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

theorem pairing_restrict_comp {S : Scheme.{u}} {A B C D U V W : Over S}
    [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj D] [GrpObj U] [GrpObj V] [GrpObj W]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (f : C ⟶ A) (g : D ⟶ B) (h : U ⟶ C) (k : V ⟶ D)
    [IsMonHom f] [IsMonHom g] [IsMonHom h] [IsMonHom k] :
    (e.restrict f g).restrict h k = e.restrict (h ≫ f) (k ≫ g) := by
  apply AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro T x y
  simp only [AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.assoc]

theorem pairingPullback_restrict {S T : Scheme.{u}} (f : T ⟶ S)
    (G H K L : Grp (Over S))
    [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj K.X] [IsCommMonObj L.X]
    (a : K ⟶ G) (b : L ⟶ H)
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f K L (e.restrict a.hom.hom b.hom.hom) =
      (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f G H e).restrict
        ((Over.pullback f).mapGrp.map a).hom.hom ((Over.pullback f).mapGrp.map b).hom.hom := by
  apply AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro Q x y
  simp only [AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue, AbelianScheme.IsogenyQuotient.PairingBaseChangeValues.Construction.nativePairingPullback_native_value]
  exact congrArg (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f Q)
    (congrArg₂ e.pairValue (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp f a Q x)
      (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp f b Q y)).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PairingPullbackRestriction
