import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubgroupStability
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperMapImmersionLocus
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup

/-! # Etale Subgroup Stability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupStability

noncomputable section

/-! A finite étale subgroup family has a constructed clopen stability
locus for an actual endomorphism of its ambient finite étale group.
The locus classifies stability after every scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {H T : Over S} [GrpObj H]
    [IsFinite H.hom] [Etale H.hom]
    {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T} (R : F.Model) (e : H ⟶ H)

def finiteEtaleSubgroupStabilityLocus : T.left.Opens := by
  let : IsFinite R.toBase.left := R.finite
  exact ProperMapImmersionLocus.properMapImmersionLocus R.toBase.left
    (lift R.toBase (R.toGroup ≫ e)).left (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left

theorem finiteEtaleSubgroupStabilityLocus_isClosed :
    IsClosed (finiteEtaleSubgroupStabilityLocus R e : Set T.left) := by
  let : IsFinite R.toBase.left := R.finite
  let : Etale R.toBase.left := AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.etale R
  exact ProperMapImmersionLocus.properMapImmersionLocus_isClosed R.toBase.left
    (lift R.toBase (R.toGroup ≫ e)).left (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left
      R.toBase.left.isOpenMap

theorem finiteEtaleSubgroupStabilityLocus_classifies
    {U : Over S} (f : U ⟶ T) :
    Set.range f.left ⊆ finiteEtaleSubgroupStabilityLocus R e ↔
      SubgroupStability.RelativeSubgroupStable (F.baseChange f) e := by
  let : IsFinite R.toBase.left := R.finite
  let a : (R.baseChange f).carrier ⟶ R.carrier := pullback.fst R.toBase f
  let b : (R.baseChange f).carrier ⟶ U := pullback.snd R.toBase f
  let v : R.carrier ⟶ T ⊗ H := lift R.toBase (R.toGroup ≫ e)
  have hs : IsPullback a.left b.left R.toBase.left f.left :=
    (IsPullback.of_hasPullback R.toBase f).map (Over.forget S)
  have ht : Set.range f.left ⊆ finiteEtaleSubgroupStabilityLocus R e ↔
      ∀ z : (R.baseChange f).carrier.left,
        v.left (a.left z) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left :=
    ProperMapImmersionLocus.schemeFiberwiseOpenLocus_baseChange R.toBase.left
      (v.left ⁻¹ᵁ ⟨Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left,
        (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left.isOpenMap.isOpen_range⟩)
      a.left b.left f.left hs
  refine ht.trans ?_
  rw [SubgroupStability.relativeSubgroupStable_iff_model (R.baseChange f) e]
  change (∀ z : (R.baseChange f).carrier.left,
      v.left (a.left z) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left) ↔
    (a ≫ R.toGroup) ≫ e ∈ F.points (R.baseChange f).carrier (b ≫ f)
  rw [AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R (b ≫ f) ((a ≫ R.toGroup) ≫ e)]
  have hp : lift (b ≫ f) ((a ≫ R.toGroup) ≫ e) = a ≫ v := by
    calc
      lift (b ≫ f) ((a ≫ R.toGroup) ≫ e) =
          lift (a ≫ R.toBase) (a ≫ (R.toGroup ≫ e)) := by
        rw [show a ≫ R.toBase = b ≫ f from pullback.condition, Category.assoc]
      _ = a ≫ v := (comp_lift a R.toBase (R.toGroup ≫ e)).symm
  rw [hp]
  constructor
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    exact h z
  · intro h z
    exact h ⟨z, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupStability
