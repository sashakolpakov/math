import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SupportBound
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedFundamentalSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Proper

/-! # Cycle Ambient Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CycleAmbientComparison

noncomputable section

/-! The finite intrinsic cone cycle pushes forward to ThomClass's actual
proper intersection cycle of the ambient cone with the embedded scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedFundamentalSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (p : ℕ) (W : X.DimensionCycleSupport p)

def coneSupport : (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).DimensionCycleSupport p :=
  ⟨SupportBound.IntegralCycle.cone X m L hL h p W,
    (Projective.ConeCodimension.of_projection X m L hL h W.val).trans W.property⟩

theorem pair_meets : Supports.ProperCycle.pairMeetsProperly (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
    p (X.ambientDimension - m) (coneSupport X m L hL h p W) (EmbeddedFundamentalSupport.support X m) := by
  intro D hD
  have hb := Proper.ambient_bound X m L hL h W.val D (by
    intro y hy
    refine ⟨(hD hy).1, ?_⟩
    exact Eq.mp (congrArg (fun S : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier => y ∈ S)
      (EmbeddedFundamentalSupport.support_range X m)) (hD hy).2)
  rw [W.property] at hb
  exact hb

def ambientCycle : (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).RationalDimensionCycle
    (p + (X.ambientDimension - m)) :=
  Supports.ProperCycle.pairCycle (Projective.Dimension.SpacePresentation.presentation X.ambientDimension) X.ambientDimension
    p (X.ambientDimension - m) (coneSupport X m L hL h p W) (EmbeddedFundamentalSupport.support X m)

theorem restrict_eq :
    Closed.EmbeddingCycle.Maps.restrict (EmbeddedFundamentalSupport.embedding X) m X.ambientDimension p (p + (X.ambientDimension - m))
      (EmbeddedFundamentalSupport.degree X m p) (ambientCycle X m L hL h p W) = SupportBound.IntegralCycle.cycle X m L hL h p W := by
  ext C
  rw [Closed.EmbeddingCycle.Maps.restrict_apply]
  rw [ambientCycle, Supports.ProperCycle.pairCycle_apply _ _ _ _ _ _ (pair_meets X m L hL h p W)]
  rfl

theorem ambient_supported :
    ∀ C ∈ (ambientCycle X m L hL h p W).support,
      (C.val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ⊆ Set.range X.embedding := by
  intro C hC
  let S : Closeds (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier :=
    ⟨Set.range X.embedding, X.embedding.isClosedEmbedding.isClosed_range⟩
  apply (Supports.supportPoint_mem_iff_subset S C.val).mp
  have hc := Finsupp.mem_support_iff.mp hC
  rw [ambientCycle, Supports.ProperCycle.pairCycle_apply _ _ _ _ _ _ (pair_meets X m L hL h p W)] at hc
  have hm : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈
      ((coneSupport X m L hL h p W).val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ∩
      ((EmbeddedFundamentalSupport.support X m).val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) := by
    by_contra hn
    exact hc (dite_eq_right hn)
  exact Eq.mp (congrArg (fun T : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier =>
    CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ T) (EmbeddedFundamentalSupport.support_range X m)) hm.2

theorem pushforward_eq :
    ProperCycleLinearity.cyclePushforward (EmbeddedFundamentalSupport.embedding X) p (p + (X.ambientDimension - m))
      (SupportBound.IntegralCycle.cycle X m L hL h p W) = ambientCycle X m L hL h p W := by
  rw [← Closed.EmbeddingCycle.Maps.embed_eq_pushforward (EmbeddedFundamentalSupport.embedding X) m X.ambientDimension p
    (p + (X.ambientDimension - m)) (EmbeddedFundamentalSupport.degree X m p), ← restrict_eq X m L hL h p W]
  exact Closed.EmbeddingCycle.Maps.embed_restrict (EmbeddedFundamentalSupport.embedding X) m X.ambientDimension p
    (p + (X.ambientDimension - m)) (EmbeddedFundamentalSupport.degree X m p) _ (ambient_supported X m L hL h p W)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CycleAmbientComparison
