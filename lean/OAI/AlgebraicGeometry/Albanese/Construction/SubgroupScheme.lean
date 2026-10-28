import OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor
import OAI.AlgebraicGeometry.Albanese.Construction.WordPoints

/-! # Subgroup Scheme -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SubgroupScheme

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

@[simp]
theorem toUnit_complexBase :
    toUnit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) = 𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  toUnit_unique _ _

/-- Restrict an ambient morphism to a reduced closed subscheme that it preserves. -/
def closedRestriction (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsReduced X.left]
    (i : X ⟶ G) [IsClosedImmersion i.left] (t : G ⟶ G)
    (ht : Set.range (i ≫ t).left ⊆ Set.range i.left) : X ⟶ X :=
  Over.homMk (ReducedFactor.factorThroughClosed i.left (i ≫ t).left ht) (by
    calc
      ReducedFactor.factorThroughClosed i.left (i ≫ t).left ht ≫ X.hom =
          ReducedFactor.factorThroughClosed i.left (i ≫ t).left ht ≫ i.left ≫ G.hom := by rw [i.w]
      _ = (i ≫ t).left ≫ G.hom := by rw [← Category.assoc, ReducedFactor.factorThroughClosed_comp]
      _ = X.hom := (i ≫ t).w)

@[reassoc (attr := simp)]
theorem closedRestriction_comp (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsReduced X.left]
    (i : X ⟶ G) [IsClosedImmersion i.left] (t : G ⟶ G)
    (ht : Set.range (i ≫ t).left ⊆ Set.range i.left) :
    closedRestriction X G i t ht ≫ i = i ≫ t := by
  ext1
  exact ReducedFactor.factorThroughClosed_comp i.left (i ≫ t).left ht

/-- Restrict an ambient automorphism when it and its inverse preserve the support. -/
def closedRestrictionIso (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsReduced X.left]
    (i : X ⟶ G) [IsClosedImmersion i.left] (t : G ≅ G)
    (ht : Set.range (i ≫ t.hom).left ⊆ Set.range i.left)
    (htinv : Set.range (i ≫ t.inv).left ⊆ Set.range i.left) : X ≅ X := by
  have : Mono i := Over.mono_of_mono_left i
  refine
    { hom := closedRestriction X G i t.hom ht
      inv := closedRestriction X G i t.inv htinv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono i).mp
    simp [Category.assoc]
  · apply (cancel_mono i).mp
    simp [Category.assoc]

@[reassoc (attr := simp)]
theorem closedRestrictionIso_hom_comp (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsReduced X.left]
    (i : X ⟶ G) [IsClosedImmersion i.left] (t : G ≅ G)
    (ht : Set.range (i ≫ t.hom).left ⊆ Set.range i.left)
    (htinv : Set.range (i ≫ t.inv).left ⊆ Set.range i.left) :
    (closedRestrictionIso X G i t ht htinv).hom ≫ i = i ≫ t.hom :=
  closedRestriction_comp X G i t.hom ht

theorem point_mulRight (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G]
    (p z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G) :
    p ≫ (GrpObj.mulRight z).hom = p * z := by
  simp [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc]

theorem point_mulRight_inv (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G]
    (p z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G) :
    p ≫ (GrpObj.mulRight z).inv = p * z⁻¹ := by
  simp [GrpObj.mulRight_inv, Hom.mul_def, Hom.inv_def, comp_lift_assoc]

/-- A translation by a point of a closed point-subgroup preserves the whole
closed subscheme set-theoretically, as does its inverse. -/
theorem translation_preserves_closed (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType G.hom] [GrpObj G]
    (i : X ⟶ G) [IsClosedImmersion i.left]
    (S : Subgroup (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G))
    (hS : ∀ q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G,
      (∃ p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X, p ≫ i = q) ↔ q ∈ S)
    (z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G) (hz : z ∈ S) :
    Set.range (i ≫ (GrpObj.mulRight z).hom).left ⊆ Set.range i.left ∧
      Set.range (i ≫ (GrpObj.mulRight z).inv).left ⊆ Set.range i.left := by
  let Z : TopologicalSpace.Closeds G.left := ⟨Set.range i.left, i.left.isClosedMap.isClosed_range⟩
  constructor
  · apply ReducedFactor.range_subset_closed_of_points X G _ Z
    intro p
    apply (ClosedPoints.pointMap_range_iff X G i _).mp
    apply (hS _).mpr
    rw [← Category.assoc, point_mulRight]
    exact S.mul_mem ((hS _).mp ⟨p, rfl⟩) hz
  · apply ReducedFactor.range_subset_closed_of_points X G _ Z
    intro p
    apply (ClosedPoints.pointMap_range_iff X G i _).mp
    apply (hS _).mpr
    rw [← Category.assoc, point_mulRight_inv]
    exact S.mul_mem ((hS _).mp ⟨p, rfl⟩) (S.inv_mem hz)

/-- The reduced closed subscheme whose rational points form a subgroup is
smooth: translations act transitively on its rational points. -/
theorem closed_point_subgroup_smooth (X G : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType G.hom] [GrpObj G]
    [IsReduced X.left] [Nonempty X.left]
    (i : X ⟶ G) [IsClosedImmersion i.left]
    (S : Subgroup (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G))
    (hS : ∀ q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G,
      (∃ p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X, p ≫ i = q) ↔ q ∈ S) : Smooth X.hom := by
  have : Mono i := Over.mono_of_mono_left i
  apply ReducedFactor.smooth_of_point_transitive X
  intro p q
  let z := (p ≫ i)⁻¹ * (q ≫ i)
  have hz : z ∈ S := S.mul_mem (S.inv_mem ((hS _).mp ⟨p, rfl⟩))
    ((hS _).mp ⟨q, rfl⟩)
  obtain ⟨ht, htinv⟩ := translation_preserves_closed X G i S hS z hz
  refine ⟨closedRestrictionIso X G i (GrpObj.mulRight z) ht htinv, ?_⟩
  apply (cancel_mono i).mp
  rw [Category.assoc, closedRestrictionIso_hom_comp, ← Category.assoc, point_mulRight]
  simp [z]

end

end OAI.AlgebraicGeometry.Albanese.Construction.SubgroupScheme
