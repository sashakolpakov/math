import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup

/-! # Perfect Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
A perfect actual scheme pairing restricts perfectly to its adjoint
direct factors. The fixed-point factors of an idempotent have constructed
retractions; neither a block duality map nor block perfection is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

section

variable {S : Scheme.{u}} {A B U V : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj U] [IsCommMonObj U] [GrpObj V] [IsCommMonObj V]

theorem Annihilator.Construction.SchemeBicharacter.restrict_isPerfect
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect)
    (i : U ⟶ A) (r : A ⟶ U) [IsMonHom i] [IsMonHom r] (hi : i ≫ r = 𝟙 U)
    (j : V ⟶ B) (s : B ⟶ V) [IsMonHom j] [IsMonHom s] (hj : j ≫ s = 𝟙 V)
    (hadj : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B),
      e.pairValue (x ≫ r ≫ i) y = e.pairValue x (y ≫ s ≫ j)) :
    (e.restrict i j).toSheafPairing.IsPerfect := by
  rw [e.toSheafPairing_restrict i j]
  let ii : Grp.mk U ⟶ Grp.mk A := Grp.homMk i
  let rr : Grp.mk A ⟶ Grp.mk U := Grp.homMk r
  let jj : Grp.mk V ⟶ Grp.mk B := Grp.homMk j
  let ss : Grp.mk B ⟶ Grp.mk V := Grp.homMk s
  have hi' : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap ii ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap rr =
      𝟙 (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk U)) := by
    rw [← CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp]
    have h : ii ≫ rr = 𝟙 (Grp.mk U) := by
      ext
      exact congrArg Over.Hom.left hi
    rw [h, CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id]
  have hj' : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap jj ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap ss =
      𝟙 (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk V)) := by
    rw [← CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp]
    have h : jj ≫ ss = 𝟙 (Grp.mk V) := by
      ext
      exact congrArg Over.Hom.left hj
    rw [h, CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id]
  apply e.toSheafPairing.restrict_isPerfect he _ _ hi' _ _ hj'
  rw [← CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp, ← CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp]
  exact e.toSheafPairing_projectorsAdjoint (r ≫ i) (s ≫ j) hadj

end

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def PerfectBlocks.Construction.fixedPointRetraction (p : A ⟶ A) [IsMonHom p] (hp : p ≫ p = p) :
    A ⟶ BlockGroups.Construction.fixedPointScheme p := BlockGroups.Construction.fixedPointLift p p hp

theorem PerfectBlocks.Construction.fixedPointRetraction_inclusion (p : A ⟶ A) [IsMonHom p] (hp : p ≫ p = p) :
    PerfectBlocks.Construction.fixedPointRetraction p hp ≫ BlockGroups.Construction.fixedPointInclusion p = p :=
  BlockGroups.Construction.fixedPointLift_inclusion p p hp

instance PerfectBlocks.Construction.fixedPointRetraction_isMonHom (p : A ⟶ A) [IsMonHom p] (hp : p ≫ p = p) :
    IsMonHom (PerfectBlocks.Construction.fixedPointRetraction p hp) := by
  exact @SupportedIntrinsicSubgroup.Construction.isMonHom_of_mono_factorization (Over S) _ _
    A (BlockGroups.Construction.fixedPointScheme p) A
    (inferInstanceAs (GrpObj A)) (inferInstanceAs (GrpObj (BlockGroups.Construction.fixedPointScheme p)))
    (inferInstanceAs (GrpObj A))
    (PerfectBlocks.Construction.fixedPointRetraction p hp) (BlockGroups.Construction.fixedPointInclusion p)
    (inferInstanceAs (IsMonHom (BlockGroups.Construction.fixedPointInclusion p)))
    (inferInstanceAs (Mono (BlockGroups.Construction.fixedPointInclusion p))) p
    (inferInstanceAs (IsMonHom p)) (PerfectBlocks.Construction.fixedPointRetraction_inclusion p hp)

theorem PerfectBlocks.Construction.fixedPointInclusion_retraction (p : A ⟶ A) [IsMonHom p] (hp : p ≫ p = p) :
    BlockGroups.Construction.fixedPointInclusion p ≫ PerfectBlocks.Construction.fixedPointRetraction p hp = 𝟙 (BlockGroups.Construction.fixedPointScheme p) := by
  apply (cancel_mono (BlockGroups.Construction.fixedPointInclusion p)).mp
  rw [Category.assoc, PerfectBlocks.Construction.fixedPointRetraction_inclusion, BlockGroups.Construction.fixedPointInclusion_fixed, Category.id_comp]

theorem PerfectBlocks.Construction.fixedPointPairing_isPerfect
    {B : Over S} [GrpObj B] [IsCommMonObj B]
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect)
    (p : A ⟶ A) (q : B ⟶ B) [IsMonHom p] [IsMonHom q]
    (hp : p ≫ p = p) (hq : q ≫ q = q)
    (hadj : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B),
      e.pairValue (x ≫ p) y = e.pairValue x (y ≫ q)) :
    (e.restrict (BlockGroups.Construction.fixedPointInclusion p) (BlockGroups.Construction.fixedPointInclusion q)).toSheafPairing.IsPerfect := by
  apply e.restrict_isPerfect he (BlockGroups.Construction.fixedPointInclusion p) (PerfectBlocks.Construction.fixedPointRetraction p hp)
    (PerfectBlocks.Construction.fixedPointInclusion_retraction p hp) (BlockGroups.Construction.fixedPointInclusion q) (PerfectBlocks.Construction.fixedPointRetraction q hq)
    (PerfectBlocks.Construction.fixedPointInclusion_retraction q hq)
  intro T x y
  rw [PerfectBlocks.Construction.fixedPointRetraction_inclusion, PerfectBlocks.Construction.fixedPointRetraction_inclusion]
  exact hadj T x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
