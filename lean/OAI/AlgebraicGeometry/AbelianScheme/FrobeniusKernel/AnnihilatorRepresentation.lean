import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeAnnihilator
import Mathlib.CategoryTheory.Sites.PreservesLimits

/-! # Annihilator Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Identify the constructed opposite group scheme with CartierDuality's annihilator
sheaf. Both restriction and the trivial character are compared on every
test scheme before transporting the equalizer.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj IsMulCommutative

universe u

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}
variable (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H) (i : H ⟶ G)

theorem CartierModel.Construction.CartierCoordinates.characterIso_apply (T : Over (Spec R)) (x : T ⟶ P.dualGroup.X) :
    P.characterIso.hom.hom.app (op T) (ULift.up x) = P.pointsEquiv T x := rfl

theorem CartierModel.Construction.CartierCoordinates.restriction_characterIso :
    (BaseChange.Construction.fppfPoints (Spec R)).map (P.restriction Q i).hom.hom ≫ Q.characterIso.hom =
      P.characterIso.hom ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction i := by
  apply Sheaf.hom_ext
  ext T x
  exact P.restriction_on_characters Q i T.unop x.down

theorem CartierModel.Construction.CartierCoordinates.trivial_characterIso :
    (BaseChange.Construction.fppfPoints (Spec R)).map (1 : P.dualGroup.X ⟶ Q.dualGroup.X) ≫ Q.characterIso.hom =
      P.characterIso.hom ≫ CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction G H := by
  apply Sheaf.hom_ext
  ext T x
  change Q.pointsEquiv T.unop (x.down ≫ (1 : P.dualGroup.X ⟶ Q.dualGroup.X)) = 1
  rw [MonObj.comp_one]
  exact (Q.pointsEquiv T.unop).map_one

theorem CartierModel.Construction.CartierCoordinates.annihilatorInclusion_restriction :
    (P.annihilatorInclusion Q i).hom.hom ≫ (P.restriction Q i).hom.hom = 1 := by
  exact (congrArg (fun f => f ≫ (P.restriction Q i).hom.hom)
    (P.annihilatorInclusion_eq Q i)).trans (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp _)

def CartierModel.Construction.CartierCoordinates.annihilatorFork : Fork (P.restriction Q i).hom.hom
    (1 : P.dualGroup.X ⟶ Q.dualGroup.X) :=
  Fork.ofι (P.annihilatorInclusion Q i).hom.hom
    ((P.annihilatorInclusion_restriction Q i).trans (MonObj.comp_one _).symm)

def CartierModel.Construction.CartierCoordinates.annihilatorForkIsLimit : IsLimit (P.annihilatorFork Q i) :=
  Fork.IsLimit.ofExistsUnique (fun t =>
    (P.annihilator_universal Q i t.pt t.ι).mp
      ((P.annihilator_condition Q i t.pt t.ι).mp
        (t.condition.trans (MonObj.comp_one t.ι))))

def CartierModel.Construction.CartierCoordinates.annihilatorEqualizerIso : (P.annihilatorGroup Q i).X ≅
    equalizer (P.restriction Q i).hom.hom (1 : P.dualGroup.X ⟶ Q.dualGroup.X) := by
  let e := (P.annihilatorForkIsLimit Q i).conePointUniqueUpToIso
    (equalizerIsEqualizer (P.restriction Q i).hom.hom (1 : P.dualGroup.X ⟶ Q.dualGroup.X))
  exact e

theorem CartierModel.Construction.CartierCoordinates.annihilatorEqualizerIso_inclusion :
    (P.annihilatorEqualizerIso Q i).hom ≫ equalizer.ι _ _ =
      (P.annihilatorInclusion Q i).hom.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (P.annihilatorForkIsLimit Q i)
    (equalizerIsEqualizer _ _) WalkingParallelPair.zero

/-- The actual finite group scheme represents the full annihilator sheaf,
including its sections on nonreduced schemes. -/
def CartierModel.Construction.CartierCoordinates.annihilatorSheafIso :
    (BaseChange.Construction.fppfPoints (Spec R)).obj (P.annihilatorGroup Q i).X ≅
      CartierDuality.CharacterSheaf.Construction.Schemes.annihilatorSheaf i :=
  (BaseChange.Construction.fppfPoints (Spec R)).mapIso (P.annihilatorEqualizerIso Q i) ≪≫
    PreservesEqualizer.iso (BaseChange.Construction.fppfPoints (Spec R)) (P.restriction Q i).hom.hom
      (1 : P.dualGroup.X ⟶ Q.dualGroup.X) ≪≫
    HasLimit.isoOfNatIso (parallelPairIso _ _ _ _ P.characterIso Q.characterIso
      (P.restriction_characterIso Q i) (P.trivial_characterIso Q))

theorem CartierModel.Construction.CartierCoordinates.annihilatorSheafIso_inclusion :
    (P.annihilatorSheafIso Q i).hom ≫ equalizer.ι
        (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction i)
        (CartierDuality.CharacterSheaf.Construction.Schemes.characterTrivialRestriction G H) =
      (BaseChange.Construction.fppfPoints (Spec R)).map (P.annihilatorInclusion Q i).hom.hom ≫
        P.characterIso.hom := by
  let F := BaseChange.Construction.fppfPoints (Spec R)
  let d := (P.restriction Q i).hom.hom
  let z : P.dualGroup.X ⟶ Q.dualGroup.X := 1
  let χ : F.obj P.dualGroup.X ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G :=
    P.characterIso.hom
  let w := parallelPairIso (F.map d) (F.map z) _ _ P.characterIso Q.characterIso
    (P.restriction_characterIso Q i) (P.trivial_characterIso Q)
  have hw : (HasLimit.isoOfNatIso w).hom ≫ equalizer.ι _ _ =
      equalizer.ι (F.map d) (F.map z) ≫ χ :=
    HasLimit.isoOfNatIso_hom_π w WalkingParallelPair.zero
  change (F.map (P.annihilatorEqualizerIso Q i).hom ≫
    ((PreservesEqualizer.iso F d z).hom ≫ (HasLimit.isoOfNatIso w).hom)) ≫ _ =
      F.map (P.annihilatorInclusion Q i).hom.hom ≫ χ
  rw [Category.assoc, Category.assoc, hw, ← Category.assoc (PreservesEqualizer.iso F d z).hom,
    PreservesEqualizer.iso_hom, equalizerComparison_comp_π,
    ← Category.assoc, ← Functor.map_comp, P.annihilatorEqualizerIso_inclusion Q i]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
