import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic

/-! # Disjoint Incidence Image -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointIncidenceImage

noncomputable section

/-! For disjoint supports the diagonal obstruction is empty. The
whole proper image of the projection-incidence locus therefore satisfies
the expected intersection dimension bound. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)

theorem first_mem (x : Support.Pair.space X W Z) : (Support.Pair.first X W Z).left x ∈ (W : Set X.carrier) := by
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) x, rfl⟩

theorem second_mem (x : Support.Pair.space X W Z) : (Support.Pair.second X W Z).left x ∈ (Z : Set X.carrier) := by
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) x, rfl⟩

theorem not_diagonal (hd : Disjoint (W : Set X.carrier) (Z : Set X.carrier)) (x : Support.Pair.space X W Z) :
    x ∉ Support.PairIncidenceStep.diagonal X W Z := by
  intro hx
  have he := Closed.Equalizer.eq_of_mem (Support.Pair.first X W Z) (Support.Pair.second X W Z) x hx
  have hw := first_mem X W Z x
  rw [he] at hw
  exact Set.disjoint_left.mp hd hw (second_mem X W Z x)

theorem not_subset_diagonal (hd : Disjoint (W : Set X.carrier) (Z : Set X.carrier))
    (C : IrreducibleCloseds (Support.Pair.space X W Z)) :
    ¬ (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.diagonal X W Z := by
  intro hC
  obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
  exact not_diagonal X W Z hd x (hC hx)

def image (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : Closeds X.carrier :=
  Proper.ImageBounds.image X (ResidualIntersection.IncidenceImage.secondMap X W Z)
    (Support.PairIncidenceStep.incidence X W Z k L)

theorem bound (hd : Disjoint (W : Set X.carrier) (Z : Set X.carrier)) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hI : Projection.Generic.InductionBounds.incidence X W Z L)
    (C : IrreducibleCloseds X.carrier) (hC : (C : Set X.carrier) ⊆ image X W Z k L) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + k ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap := by
  apply Proper.ImageBounds.bound X (ResidualIntersection.IncidenceImage.secondMap X W Z)
    (Support.PairIncidenceStep.incidence X W Z k L) k
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap) ?_ C hC
  rw [ResidualIntersection.IncidenceImage.second_over]
  intro D hD
  exact hI D hD (not_subset_diagonal X W Z hd D)

theorem image_subset (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    (image X W Z k L : Set X.carrier) ⊆ (Z : Set X.carrier) := by
  rintro _ ⟨x, _, rfl⟩
  exact second_mem X W Z x

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointIncidenceImage
