import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleMembershipDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity

/-! # Split Subgroup Detection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitSubgroupDetection

noncomputable section

/-! For an actually split finite etale group over a field, its rational
subgroup points determine the entire modeled subgroup on every test
scheme. The proof uses open subgroup models and actual point coverage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity.Lifts

universe u

section FieldTests

variable {S : Scheme.{u}} {H P : Over S} [GrpObj H] [IsFinite H.hom] [Etale H.hom]
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H P} (R : F.Model)

theorem field_membership_iff (k : Type u) [Field k] (s : Spec (.of k) ⟶ S)
    (t : Over.mk s ⟶ P) (a : Over.mk s ⟶ H) :
    a ∈ F.points (Over.mk s) t ↔
      (lift t a).left (IsLocalRing.closedPoint k) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left := by
  rw [AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R t a]
  constructor
  · intro h
    exact h ⟨IsLocalRing.closedPoint k, rfl⟩
  · intro h z hz
    obtain ⟨x, rfl⟩ := hz
    have hx : x = IsLocalRing.closedPoint k :=
      @Subsingleton.elim (Spec (.of k)) inferInstance x _
    simpa only [hx] using h

end FieldTests

variable {k : Type u} [Field k] {I : Type u} {H : Over (Spec (.of k))}
  [GrpObj H] [IsFinite H.hom] [Etale H.hom]
  (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ H)
  {F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H (Over.mk (𝟙 (Spec (.of k))))} (R : F.Model) (R' : G.Model)

include e R R' in
theorem eq_of_split_rational_points
    (h : F.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _) = G.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _)) : F = G := by
  apply AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels.eq_of_geometric_points R R'
  intro K _ _ s t
  ext a
  obtain ⟨i, hi⟩ := SplitPointSurjectivity.Lifts.splitLabelPoint_covers e (a.left (IsLocalRing.closedPoint K))
  let r : Over.mk (𝟙 (Spec (.of k))) ⟶ H := SplitPointSurjectivity.Lifts.splitLabelPoint e i
  have hp : (lift t a).left (IsLocalRing.closedPoint K) =
      (lift (𝟙 (Over.mk (𝟙 (Spec (.of k))))) r).left (IsLocalRing.closedPoint k) := by
    let uH : Over.mk (𝟙 (Spec (.of k))) ⊗ H ≅ H := λ_ H
    have : IsIso uH.hom.left := (Over.forget _).map_isIso uH.hom
    apply uH.hom.left.homeomorph.injective
    change ((lift t a) ≫ snd _ H).left (IsLocalRing.closedPoint K) =
      ((lift (𝟙 _) r) ≫ snd _ H).left (IsLocalRing.closedPoint k)
    simpa only [lift_snd] using hi.symm
  rw [field_membership_iff R K s t a, hp,
    ← field_membership_iff R k (𝟙 (Spec (.of k))) (𝟙 _) r,
    h, field_membership_iff R' k (𝟙 (Spec (.of k))) (𝟙 _) r,
    ← hp, ← field_membership_iff R' K s t a]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitSubgroupDetection
