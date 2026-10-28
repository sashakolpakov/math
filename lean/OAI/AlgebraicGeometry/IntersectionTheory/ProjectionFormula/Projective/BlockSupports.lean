import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointProjectiveBlocks
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedFundamentalSupport

/-! # Block Supports -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports

noncomputable section

/-! Supports from a projective presentation and from a projective
base can be placed in disjoint blocks without changing their dimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

def ambient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation :=
  Dimension.SpacePresentation.presentation (X.ambientDimension + r + 1)

def source (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) : X.toOver ⟶ (ambient X r).toOver :=
  Over.homMk (X.embedding ≫ DisjointProjectiveBlocks.left X.ambientDimension r) (by
    change (X.embedding ≫ DisjointProjectiveBlocks.left X.ambientDimension r) ≫
      Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (X.ambientDimension + r + 1) = X.structureMap
    rw [Category.assoc, DisjointProjectiveBlocks.left_over, X.embedding_over])

def target (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) :
    (Dimension.SpacePresentation.presentation r).toOver ⟶ (ambient X r).toOver :=
  Over.homMk (DisjointProjectiveBlocks.right X.ambientDimension r)
    (DisjointProjectiveBlocks.right_over X.ambientDimension r)

instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) : IsClosedImmersion (source X r).left := by
  change IsClosedImmersion (X.embedding ≫ DisjointProjectiveBlocks.left X.ambientDimension r)
  infer_instance

instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) : IsClosedImmersion (target X r).left :=
  inferInstanceAs (IsClosedImmersion (DisjointProjectiveBlocks.right X.ambientDimension r))

theorem source_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) (W : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport (source X r) W) (ambient X r).structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap :=
  PushforwardComposition.Grading.support_dimension_eq_of_degree (source X r) W (by
    rw [Principal.ClosedSectionCycle.residueDegree_immersion]; exact Nat.one_ne_zero)

theorem target_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ)
    (S : IrreducibleCloseds (Dimension.SpacePresentation.presentation r).carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport (target X r) S) (ambient X r).structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension S (Dimension.SpacePresentation.presentation r).structureMap :=
  PushforwardComposition.Grading.support_dimension_eq_of_degree (target X r) S (by
    rw [Principal.ClosedSectionCycle.residueDegree_immersion]; exact Nat.one_ne_zero)

theorem disjoint (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) (W : IrreducibleCloseds X.carrier)
    (S : IrreducibleCloseds (Dimension.SpacePresentation.presentation r).carrier) :
    Disjoint (ProperCycleLinearity.imageSupport (source X r) W : Set (ambient X r).carrier)
      (ProperCycleLinearity.imageSupport (target X r) S : Set (ambient X r).carrier) := by
  rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image, Set.disjoint_left]
  rintro _ ⟨x, _, rfl⟩ ⟨y, _, he⟩
  have hd := DisjointProjectiveBlocks.ranges_disjoint X.ambientDimension r
  rw [Set.disjoint_left] at hd
  exact hd (Set.mem_range_self (X.embedding x)) ⟨y, he⟩

def sourceWhole (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] (r : ℕ) :
    IrreducibleCloseds (ambient X r).carrier := ProperCycleLinearity.imageSupport (source X r) (Integral.Fundamental.whole X)

def targetWhole (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) :
    IrreducibleCloseds (ambient X r).carrier :=
  ProperCycleLinearity.imageSupport (target X r) (Integral.Fundamental.whole (Dimension.SpacePresentation.presentation r))

theorem sourceWhole_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m r : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (sourceWhole X r) (ambient X r).structureMap = m := by
  rw [sourceWhole, source_dimension]
  have he := Grading.supportDimension_add_codimension X m (Integral.Fundamental.whole X)
  rw [Integral.Fundamental.whole_codimension X m, add_zero] at he
  exact he

theorem targetWhole_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (targetWhole X r) (ambient X r).structureMap = r := by
  rw [targetWhole, target_dimension]
  have he := Grading.supportDimension_add_codimension (Dimension.SpacePresentation.presentation r) r
    (Integral.Fundamental.whole (Dimension.SpacePresentation.presentation r))
  rw [Integral.Fundamental.whole_codimension _ r, add_zero] at he
  exact he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports
