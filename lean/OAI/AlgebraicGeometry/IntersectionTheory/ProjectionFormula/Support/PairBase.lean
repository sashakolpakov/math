import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearCutDimension

/-! # Pair Base -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairBase

noncomputable section

/-! The shared base locus for a pair of supports is the product
of their two linear base loci, so the two dimension drops add. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)

def factor {k : ℕ} (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    Closeds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
  Projective.LinearCut.commonZero (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (fun i => (L i).val)

def both (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : Closeds (Pair.space X W Z) :=
  CoincidenceBaseLocus.bothBase X k L (Pair.first X W Z) (Pair.second X W Z)

theorem both_eq (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    (both X W Z k L : Set (Pair.space X W Z)) =
      pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) ⁻¹'
        (factor X W L : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ∩
      pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) ⁻¹'
        (factor X Z L : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) := by
  ext x
  change (¬ (Pair.first X W Z).left x ∈ PartialLinear.Projection.domain X k L) ∧
      (¬ (Pair.second X W Z).left x ∈ PartialLinear.Projection.domain X k L) ↔
    pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) x ∈
      Projective.LinearCut.commonZero (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (fun i => (L i).val) ∧
    pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) x ∈
      Projective.LinearCut.commonZero (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.embedding) (fun i => (L i).val)
  rw [PartialLinear.Projection.mem_domain, PartialLinear.Projection.mem_domain,
    Projective.LinearCut.mem_commonZero, Projective.LinearCut.mem_commonZero]
  simp only [not_exists, not_not]
  rfl

theorem bound (k : ℕ) (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (a b r s : ℕ)
    (hW : ∀ C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W),
      (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ⊆ factor X W L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) + a ≤ r)
    (hZ : ∀ C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z),
      (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) ⊆ factor X Z L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) + b ≤ s)
    (C : IrreducibleCloseds (Pair.space X W Z)) (hC : (C : Set (Pair.space X W Z)) ⊆ both X W Z k L) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Pair.base X W Z) + (a + b) ≤ r + s := by
  apply Closed.ProductSupport.Bounds.bound (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap)
    (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) (factor X W L) (factor X Z L) a b r s hW hZ C
  exact hC.trans_eq (both_eq X W Z k L)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairBase
