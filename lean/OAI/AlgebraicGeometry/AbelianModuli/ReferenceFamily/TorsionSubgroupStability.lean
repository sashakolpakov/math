import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubgroupStability
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Subgroups

/-! # Torsion Subgroup Stability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionSubgroupStability

noncomputable section

/-! Every actual group endomorphism restricts to the torsion equalizer.
For a killed subgroup, stability is unchanged by viewing the subgroup
inside that torsion scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (e : A ⟶ A) [IsMonHom e]

def torsionEndomorphism : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n ⟶ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ e) (by
    have hi : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ^ n = 1 :=
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
        ⟨𝟙 (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n), Category.id_comp _⟩
    rw [← MonObj.pow_comp, hi, MonObj.one_comp])

theorem torsionEndomorphism_inclusion :
    torsionEndomorphism A n e ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n = AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ e :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

theorem relativeSubgroupStable_torsion_iff {T : Over S}
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A T) (hF : F.KilledBy n) :
    SubgroupStability.RelativeSubgroupStable (AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups.restrict A n F) (torsionEndomorphism A n e) ↔
      SubgroupStability.RelativeSubgroupStable F e := by
  constructor
  · intro h X t a ha
    let b := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n a (hF X t a ha)
    have hb : b ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n = a := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _
    have hm : b ∈ (AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups.restrict A n F).points X t := by
      change b ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ∈ F.points X t
      rwa [hb]
    have hs := h X t b hm
    change (b ≫ torsionEndomorphism A n e) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ∈ F.points X t at hs
    rw [Category.assoc, torsionEndomorphism_inclusion, ← Category.assoc, hb] at hs
    exact hs
  · intro h X t a ha
    change a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ∈ F.points X t at ha
    change (a ≫ torsionEndomorphism A n e) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ∈ F.points X t
    rw [Category.assoc, torsionEndomorphism_inclusion, ← Category.assoc]
    exact h X t (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) ha

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionSubgroupStability
