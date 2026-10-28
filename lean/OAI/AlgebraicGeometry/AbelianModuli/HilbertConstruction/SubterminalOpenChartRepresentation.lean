import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalRelativeChart
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Subterminal Open Chart Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartRepresentation

noncomputable section

/-! A representation of the restriction of a subterminal presheaf to an open base chart defines a relatively representable open immersion into that presheaf. Its pullback to each test is the actual open base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S U : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (i : U ⟶ S) (M : Over U)
variable (e : (Over.map i).op ⋙ F ≅ yoneda.obj M)

def restrictedRepresentedChartMap : yoneda.obj ((Over.map i).obj M) ⟶ F :=
  yonedaEquiv.symm (e.inv.app (.op M) (𝟙 M))

def restrictedRepresentedChartPullbackArrow (T : Over S) (β : yoneda.obj T ⟶ F) :
    SubterminalRelativeChart.baseChartTest i T ⟶ (Over.map i).obj M :=
  (Over.map i).map (e.hom.app (.op ((Over.pullback i).obj T))
    (F.map (SubterminalRelativeChart.baseChartProjection i T).op (yonedaEquiv β)))

theorem restrictedRepresentedChart_isOpenImmersion [IsOpenImmersion i] [Mono M.hom]
    (hs : ∀ T : Over S, Subsingleton (F.obj (.op T))) :
    (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).presheaf (restrictedRepresentedChartMap F i M e) := by
  have : (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).RespectsIso :=
    inferInstanceAs (((IsOpenImmersion : MorphismProperty Scheme.{u}).inverseImage
      (Over.forget S)).RespectsIso)
  apply MorphismProperty.relative.of_exists
  intro T β
  let L := SubterminalRelativeChart.baseChartTest i T
  let r := SubterminalRelativeChart.baseChartProjection i T
  let a := restrictedRepresentedChartPullbackArrow F i M e T β
  have hr : Mono r := SubterminalRelativeChart.baseChartProjection_mono i T
  refine ⟨L, yoneda.map a, r, ?_, SubterminalRelativeChart.baseChartProjection_open i T⟩
  apply IsPullback.of_forall_isPullback_app
  intro V
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    exact @Subsingleton.elim _ (hs V.unop) _ _
  · intro x y hxy
    exact (cancel_mono r).mp hxy.2
  · intro x y _
    exact ⟨SubterminalRelativeChart.baseChartTestLift i T M x y,
      SubterminalRelativeChart.baseChartTestLift_toChart i T M x y a, SubterminalRelativeChart.baseChartTestLift_projection i T M x y⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartRepresentation
