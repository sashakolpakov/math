import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimage
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroupCover

/-! # Subgroup Preimage Projector -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageProjector.Construction

noncomputable section

/-! A source coefficient endomorphism acts on the subgroup preimage,
fixing its target projection. Idempotence on the bounded preimage is enough
for the resulting fixed subgroup to remain a finite flat cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {A B J : Grp (Over S)}
  (f : A ⟶ B) (j : J ⟶ B) (a : A ⟶ A) (b : B ⟶ B)
  (hab : a ≫ f = f ≫ b) (hj : j ≫ b = j)

def subgroupPreimageEndomorphism : SubgroupPreimage.Construction.subgroupPreimage f j ⟶ SubgroupPreimage.Construction.subgroupPreimage f j :=
  pullback.lift (SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a) (SubgroupPreimage.Construction.subgroupPreimageProjection f j) (by
    rw [Category.assoc, hab, ← Category.assoc, pullback.condition, Category.assoc, hj])

theorem subgroupPreimageEndomorphism_inclusion :
    subgroupPreimageEndomorphism f j a b hab hj ≫ SubgroupPreimage.Construction.subgroupPreimageInclusion f j =
      SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a := pullback.lift_fst _ _ _

theorem subgroupPreimageEndomorphism_projection :
    subgroupPreimageEndomorphism f j a b hab hj ≫ SubgroupPreimage.Construction.subgroupPreimageProjection f j =
      SubgroupPreimage.Construction.subgroupPreimageProjection f j := pullback.lift_snd _ _ _

theorem subgroupPreimageEndomorphism_idempotent
    (ha : (SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a) ≫ a = SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a) :
    subgroupPreimageEndomorphism f j a b hab hj ≫ subgroupPreimageEndomorphism f j a b hab hj =
      subgroupPreimageEndomorphism f j a b hab hj := by
  apply pullback.hom_ext
  · rw [Category.assoc, subgroupPreimageEndomorphism_inclusion, ← Category.assoc,
      subgroupPreimageEndomorphism_inclusion, ha]
  · rw [Category.assoc, subgroupPreimageEndomorphism_projection, subgroupPreimageEndomorphism_projection]

include hab hj in
theorem subgroupPreimageFixed_cover
    [IsFinite f.hom.hom.left] [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]
    [Surjective f.hom.hom.left]
    (ha : (SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a) ≫ a = SubgroupPreimage.Construction.subgroupPreimageInclusion f j ≫ a) :
    let G := SubgroupPreimage.Construction.subgroupPreimage f j
    let e := subgroupPreimageEndomorphism f j a b hab hj
    let p := SubgroupPreimage.Construction.subgroupPreimageProjection f j
    IsFinite (FixedGroupCover.Construction.fixedGroupTargetOver G e p).hom ∧
      Flat (FixedGroupCover.Construction.fixedGroupTargetOver G e p).hom ∧
      LocallyOfFinitePresentation (FixedGroupCover.Construction.fixedGroupTargetOver G e p).hom ∧
      Surjective (FixedGroupCover.Construction.fixedGroupTargetOver G e p).hom := by
  obtain ⟨hf, hflat, hfp, hsurj⟩ := SubgroupPreimage.Construction.subgroupPreimageProjection_cover f j
  let := hf
  let := hflat
  let := hfp
  let := hsurj
  exact FixedGroupCover.Construction.fixedGroupProjection_cover _ _ (subgroupPreimageEndomorphism_idempotent f j a b hab hj ha)
    _ (subgroupPreimageEndomorphism_projection f j a b hab hj)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimageProjector.Construction
