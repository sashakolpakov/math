import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupTransferIff
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group

/-! # Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups

/-! Genuine killed subgroup families are exactly subgroup families of actual torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
variable {T : Over S}

instance torsionInclusion_mono : Mono (SubgroupFunctor.torsionι A n) := by
  unfold SubgroupFunctor.torsionι
  exact Limits.equalizer.ι_mono (f := ((𝟙 A : A ⟶ A) ^ n)) (g := (1 : A ⟶ A))

noncomputable abbrev restrict (F : SubgroupFunctor.RelativeSubgroup A T) : SubgroupFunctor.RelativeSubgroup (SubgroupFunctor.torsionScheme A n) T :=
  SubgroupTransferIff.SubgroupTransfer.comap (SubgroupFunctor.torsionι A n) F

noncomputable abbrev extend (F : SubgroupFunctor.RelativeSubgroup (SubgroupFunctor.torsionScheme A n) T) : SubgroupFunctor.RelativeSubgroup A T :=
  SubgroupTransferIff.SubgroupTransfer.map (SubgroupFunctor.torsionι A n) F

theorem extend_restrict (F : SubgroupFunctor.RelativeSubgroup A T) (hF : F.KilledBy n) :
    extend A n (restrict A n F) = F := by
  ext X t a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hba ▸ hb
  · intro ha
    let b := SubgroupFunctor.torsionLift n a (hF X t a ha)
    refine ⟨b, ?_, SubgroupFunctor.torsionLift_ι _ _ _⟩
    change b ≫ SubgroupFunctor.torsionι A n ∈ F.points X t
    rw [SubgroupFunctor.torsionLift_ι]
    exact ha

noncomputable def restrictModel {F : SubgroupFunctor.RelativeSubgroup A T} (R : F.Model) (hF : F.KilledBy n) :
    (restrict A n F).Model where
  carrier := R.carrier
  toBase := R.toBase
  toGroup := R.toTorsion hF
  finite := R.finite
  flat := R.flat
  finitePresentation := R.finitePresentation
  jointly_monic := by
    intro X h k hb hg
    apply R.jointly_monic X h k hb
    have he := congrArg (fun f => f ≫ SubgroupFunctor.torsionι A n) hg
    simpa only [Category.assoc, SubgroupFunctor.RelativeSubgroup.Model.toTorsion_ι] using he
  points_iff := by
    intro X t b
    change b ≫ SubgroupFunctor.torsionι A n ∈ F.points X t ↔ _
    rw [R.points_iff]
    constructor
    · rintro ⟨h, ht, hg⟩
      refine ⟨h, ht, ?_⟩
      apply (cancel_mono (SubgroupFunctor.torsionι A n)).mp
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => h ≫ f) (R.toTorsion_ι hF)).trans hg)
    · rintro ⟨h, ht, hg⟩
      refine ⟨h, ht, ?_⟩
      exact (congrArg (fun f => h ≫ f) (R.toTorsion_ι hF)).symm.trans
        (((Category.assoc _ _ _).symm).trans (congrArg (fun f => f ≫ SubgroupFunctor.torsionι A n) hg))

noncomputable def restrictPointsEquiv (F : SubgroupFunctor.RelativeSubgroup A T) (hF : F.KilledBy n)
    (X : Over S) (t : X ⟶ T) : (restrict A n F).points X t ≃* F.points X t :=
  (SubgroupTransferIff.SubgroupTransfer.pointsEquiv (SubgroupFunctor.torsionι A n) (restrict A n F) X t).trans
    (MulEquiv.subgroupCongr (congrArg (fun G : SubgroupFunctor.RelativeSubgroup A T => G.points X t)
      (extend_restrict A n F hF)))

theorem extend_killed (F : SubgroupFunctor.RelativeSubgroup (SubgroupFunctor.torsionScheme A n) T) : (extend A n F).KilledBy n := by
  intro X t a ha
  obtain ⟨b, _, hba⟩ := ha
  exact (SubgroupFunctor.factors_through_torsion_iff n a).mp ⟨b, hba⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups
