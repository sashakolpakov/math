import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction

/-! # Torsion Pairing Inclusion Squares -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingInclusionSquares

noncomputable section

/-! Ambient inclusion squares determine the corresponding maps into
native torsion, and hence the restrictions of the original pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction
attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

universe u

theorem torsionPairingBaseChangeMap_inclusion {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)
    (K : Grp (Over S)) (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) :
    (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f G n K a).hom.hom ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback f).obj G.X) n =
        (Over.pullback f).map (a.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n) := by
  let aRaw : K.X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n := a.hom.hom
  change ((Over.pullback f).map aRaw ≫ (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso f G n).hom) ≫ _ =
    (Over.pullback f).map (aRaw ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Over.pullback f).map aRaw ≫ z)
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso_inclusion f G n)).trans
      ((Over.pullback f).map_comp aRaw (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n)).symm)

theorem torsion_inclusion_square {S : Scheme.{u}} {A B K L : Over S}
    [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    (n : ℕ) (f : A ⟶ B) [IsMonHom f]
    (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n)
    (k : K ⟶ L)
    (h : k ≫ b ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n =
      a ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n ≫ f) :
    k ≫ b = a ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f := by
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)).mp
  exact (Category.assoc _ _ _).trans
    (h.trans ((congrArg (fun z => a ≫ z) (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion n f).symm).trans
      (Category.assoc _ _ _).symm))

theorem torsion_pairing_restriction_square {S : Scheme.{u}} {A B K L U V : Over S}
    [GrpObj A] [GrpObj B] [GrpObj K] [GrpObj L] [GrpObj U] [GrpObj V]
    [IsCommMonObj A] [IsCommMonObj B]
    (n : ℕ) (f : A ⟶ B) [IsMonHom f]
    (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n)
    (c : U ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (d : V ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n)
    (k : K ⟶ L) (r : U ⟶ V)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] [IsMonHom d] [IsMonHom k] [IsMonHom r]
    (eA : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (eB : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (hk : k ≫ b ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n = a ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n ≫ f)
    (hr : r ≫ d ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n = c ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n ≫ f)
    (he : ∀ (T : Over S) (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n),
      eB.pairValue (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) = eA.pairValue x y) :
    (eB.restrict b d).restrict k r = eA.restrict a c := by
  have hk' := torsion_inclusion_square n f a b k hk
  have hr' := torsion_inclusion_square n f c d r hr
  apply AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro T x y
  simp only [AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.assoc, hk', hr']
  simpa only [Category.assoc] using he T (x ≫ a) (y ≫ c)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingInclusionSquares
