import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairBase
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceDimensionStep

/-! # Pair Incidence Step -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairIncidenceStep

noncomputable section

/-! The dimension induction for projection coincidences on a pair
of cycle supports, with the actual shared base locus accounted for. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)

def incidence (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    Closeds (Pair.space X W Z) :=
  Projection.Coincidence.locus X k L (Pair.first X W Z) (Pair.second X W Z)

def diagonal : Closeds (Pair.space X W Z) := Closed.Equalizer.locus (Pair.first X W Z) (Pair.second X W Z)

theorem step (k r s : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hW : ∀ C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W),
      (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ⊆ PairBase.factor X W L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) + (k + 1) ≤ r)
    (hZ : ∀ C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z),
      (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) ⊆ PairBase.factor X Z L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) + (k + 1) ≤ s)
    (hI : ∀ C : IrreducibleCloseds (Pair.space X W Z),
      (C : Set (Pair.space X W Z)) ⊆ incidence X W Z k L →
      ¬ (C : Set (Pair.space X W Z)) ⊆ diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Pair.base X W Z) + k ≤ r + s)
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (ha : ∀ C : irreducibleComponents (incidence X W Z k L),
      ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (Pair.space X W Z) (incidence X W Z k L) C : Set (Pair.space X W Z)) ⊆ diagonal X W Z →
      ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport (Pair.space X W Z) (incidence X W Z k L) C,
        x ∉ incidence X W Z (k + 1) (Fin.cons a L)) :
    ∀ C : IrreducibleCloseds (Pair.space X W Z),
      (C : Set (Pair.space X W Z)) ⊆ incidence X W Z (k + 1) (Fin.cons a L) →
      ¬ (C : Set (Pair.space X W Z)) ⊆ diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Pair.base X W Z) + (k + 1) ≤ r + s := by
  have hRS : (incidence X W Z (k + 1) (Fin.cons a L) : Set (Pair.space X W Z)) ⊆
      incidence X W Z k L ⊔ PairBase.both X W Z k L :=
    CoincidenceBaseLocus.subset X k L (Pair.first X W Z) (Pair.second X W Z) a
  apply IncidenceDimensionStep.step (Pair.base X W Z) (incidence X W Z k L)
    (incidence X W Z (k + 1) (Fin.cons a L)) (PairBase.both X W Z k L)
    (diagonal X W Z) k (r + s) hRS hI
  · intro C hC _
    have hb := PairBase.bound X W Z k L (k + 1) (k + 1) r s hW hZ C hC
    omega
  · intro C hC _
    exact ha C hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairIncidenceStep
