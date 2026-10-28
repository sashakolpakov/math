import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Subgroup Transfer Iff -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupTransferIff.SubgroupTransfer

/-! Images and inverse images of actual relative subgroup functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H A T : Over S} [GrpObj H] [GrpObj A]
variable (j : H ⟶ A) [IsMonHom j]

noncomputable def postcompose (X : Over S) : (X ⟶ H) →* (X ⟶ A) where
  toFun a := a ≫ j
  map_one' := MonObj.one_comp j
  map_mul' a b := MonObj.mul_comp a b j

noncomputable def map (F : SubgroupFunctor.RelativeSubgroup H T) : SubgroupFunctor.RelativeSubgroup A T where
  points X t := (F.points X t).map (postcompose j X)
  naturality := by
    intro X Y f t a ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨f ≫ b, F.naturality f t hb, Category.assoc f b j⟩

noncomputable def comap (F : SubgroupFunctor.RelativeSubgroup A T) : SubgroupFunctor.RelativeSubgroup H T where
  points X t := (F.points X t).comap (postcompose j X)
  naturality := by
    intro X Y f t a ha
    have h := F.naturality f t ha
    change (f ≫ a) ≫ j ∈ F.points X (f ≫ t)
    change f ≫ (a ≫ j) ∈ F.points X (f ≫ t) at h
    exact (Category.assoc f a j).symm ▸ h

theorem map_mem_iff (F : SubgroupFunctor.RelativeSubgroup H T) (X : Over S) (t : X ⟶ T) (a : X ⟶ A) :
    a ∈ (SubgroupTransfer.map j F).points X t ↔ ∃ b : X ⟶ H, b ∈ F.points X t ∧ b ≫ j = a := Iff.rfl

theorem comap_mem_iff (F : SubgroupFunctor.RelativeSubgroup A T) (X : Over S) (t : X ⟶ T) (a : X ⟶ H) :
    a ∈ (SubgroupTransfer.comap j F).points X t ↔ a ≫ j ∈ F.points X t := Iff.rfl

@[simp]
theorem map_baseChange (F : SubgroupFunctor.RelativeSubgroup H T) {U : Over S} (f : U ⟶ T) :
    (SubgroupTransfer.map j F).baseChange f = SubgroupTransfer.map j (F.baseChange f) := rfl

@[simp]
theorem comap_baseChange (F : SubgroupFunctor.RelativeSubgroup A T) {U : Over S} (f : U ⟶ T) :
    (SubgroupTransfer.comap j F).baseChange f = SubgroupTransfer.comap j (F.baseChange f) := rfl

variable [Mono j]

theorem postcompose_injective (X : Over S) : Function.Injective (postcompose j X) :=
  fun _ _ h => (cancel_mono j).mp h

@[simp]
theorem comap_map (F : SubgroupFunctor.RelativeSubgroup H T) : SubgroupTransfer.comap j (SubgroupTransfer.map j F) = F := by
  ext X t a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ((cancel_mono j).mp hba) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

noncomputable def pointsEquiv (F : SubgroupFunctor.RelativeSubgroup H T) (X : Over S) (t : X ⟶ T) :
    F.points X t ≃* (SubgroupTransfer.map j F).points X t :=
  (F.points X t).equivMapOfInjective (postcompose j X) (postcompose_injective j X)

noncomputable def mapModel {F : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model) : (SubgroupTransfer.map j F).Model where
  carrier := R.carrier
  toBase := R.toBase
  toGroup := R.toGroup ≫ j
  finite := R.finite
  flat := R.flat
  finitePresentation := R.finitePresentation
  jointly_monic := by
    intro X h k hb hg
    apply R.jointly_monic X h k hb
    apply (cancel_mono j).mp
    simpa only [Category.assoc] using hg
  points_iff := by
    intro X t a
    rw [map_mem_iff]
    constructor
    · rintro ⟨b, hb, hba⟩
      obtain ⟨h, ht, hg⟩ := (R.points_iff X t b).mp hb
      refine ⟨h, ht, ?_⟩
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ j) hg).trans hba)
    · rintro ⟨h, ht, hg⟩
      exact ⟨h ≫ R.toGroup, (R.points_iff X t _).mpr ⟨h, ht, rfl⟩,
        (Category.assoc _ _ _).trans hg⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupTransferIff.SubgroupTransfer
