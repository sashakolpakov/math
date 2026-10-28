import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartsCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentability

/-! # General Restricted Represented Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneralRestrictedRepresentedCharts

noncomputable section

/-! A representation over an open part of the base defines a representable
open chart of any presheaf. No subterminality of the presheaf or of its
representing scheme is needed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

private theorem yonedaNat_precomp {C : Type v} [Category.{u} C]
    {F : Cᵒᵖ ⥤ Type u} {X Y Z : C} (α : yoneda.obj X ⟶ F) (a : Y ⟶ Z) (b : Z ⟶ X) :
    α.app (.op Y) (a ≫ b) = F.map a.op (α.app (.op Z) b) :=
  NatTrans.naturality_apply α a.op b

variable {S U : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
  (i : U ⟶ S) (M : Over U)
  (e : (Over.map i).op ⋙ F ≅ yoneda.obj M)

theorem restrictedRepresentedChartMap_onMap {V : Over U} (a : V ⟶ M) :
    (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e).app (.op ((Over.map i).obj V))
      ((Over.map i).map a) = e.inv.app (.op V) a := by
  change F.map ((Over.map i).map a).op (e.inv.app (.op M) (𝟙 M)) = _
  have hn : e.inv.app (.op V) (a ≫ 𝟙 M) =
      F.map ((Over.map i).map a).op (e.inv.app (.op M) (𝟙 M)) :=
    NatTrans.naturality_apply e.inv a.op (𝟙 M)
  exact hn.symm.trans (congrArg (fun b : V ⟶ M => e.inv.app (.op V) b) (Category.comp_id a))

theorem restrictedRepresentedChartMap_injective [Mono i] (V : Over S) :
    Function.Injective ((SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e).app (.op V)) := by
  intro a b hab
  let W : Over U := Over.mk (a.left ≫ M.hom)
  let q : (Over.map i).obj W ≅ V :=
    Over.isoMk (Iso.refl V.left) (by
      change (𝟙 V.left) ≫ V.hom = (a.left ≫ M.hom) ≫ i
      rw [Category.id_comp, Category.assoc]
      exact a.w.symm)
  let a' : W ⟶ M := Over.homMk a.left
  let b' : W ⟶ M := Over.homMk b.left (by
    apply (cancel_mono i).mp
    exact ((Category.assoc b.left M.hom i).trans b.w).trans
      ((Category.assoc a.left M.hom i).trans a.w).symm)
  have ha : (Over.map i).map a' = q.hom ≫ a := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp a.left).symm
  have hb : (Over.map i).map b' = q.hom ≫ b := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp b.left).symm
  have h : e.inv.app (.op W) a' = e.inv.app (.op W) b' := by
    rw [← restrictedRepresentedChartMap_onMap F i M e a',
      ← restrictedRepresentedChartMap_onMap F i M e b', ha, hb]
    exact (yonedaNat_precomp (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e) q.hom a).trans
      ((congrArg (F.map q.hom.op) hab).trans
        (yonedaNat_precomp (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e) q.hom b).symm)
  have h' : a' = b' := (e.app (.op W)).toEquiv.symm.injective h
  apply Over.OverMorphism.ext
  exact congrArg (fun z : W ⟶ M => z.left) h'

theorem restrictedRepresentedChartPullbackArrow_value
    (T : Over S) (β : yoneda.obj T ⟶ F) :
    (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e).app (.op (SubterminalRelativeChart.baseChartTest i T))
        (SubterminalOpenChartRepresentation.restrictedRepresentedChartPullbackArrow F i M e T β) =
      β.app (.op (SubterminalRelativeChart.baseChartTest i T)) (SubterminalRelativeChart.baseChartProjection i T) := by
  let V := (Over.pullback i).obj T
  let s : ((Over.map i).op ⋙ F).obj (.op V) :=
    F.map (SubterminalRelativeChart.baseChartProjection i T).op (yonedaEquiv β)
  have h₁ := restrictedRepresentedChartMap_onMap F i M e (e.hom.app (.op V) s)
  have h₂ : e.inv.app (.op V) (e.hom.app (.op V) s) = s :=
    (e.app (.op V)).toEquiv.symm_apply_apply s
  have h₃ : F.map (SubterminalRelativeChart.baseChartProjection i T).op (yonedaEquiv β) =
      β.app (.op (SubterminalRelativeChart.baseChartTest i T)) (SubterminalRelativeChart.baseChartProjection i T) :=
    (yonedaNat_precomp β (SubterminalRelativeChart.baseChartProjection i T) (𝟙 T)).symm.trans
      (congrArg (fun a : SubterminalRelativeChart.baseChartTest i T ⟶ T => β.app (.op (SubterminalRelativeChart.baseChartTest i T)) a)
        (Category.comp_id (SubterminalRelativeChart.baseChartProjection i T)))
  exact h₁.trans (h₂.trans h₃)

theorem generalRestrictedRepresentedChart_isOpenImmersion [IsOpenImmersion i] :
    (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).presheaf (SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e) := by
  have : (Relative.RepresentableOpenGlueData.relativeOpenImmersions S).RespectsIso :=
    inferInstanceAs (((IsOpenImmersion : MorphismProperty Scheme.{u}).inverseImage
      (Over.forget S)).RespectsIso)
  apply MorphismProperty.relative.of_exists
  intro T β
  let L := SubterminalRelativeChart.baseChartTest i T
  let r := SubterminalRelativeChart.baseChartProjection i T
  let a := SubterminalOpenChartRepresentation.restrictedRepresentedChartPullbackArrow F i M e T β
  let α := SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F i M e
  have hr : Mono r := SubterminalRelativeChart.baseChartProjection_mono i T
  have hvalue : α.app (.op L) a = β.app (.op L) r :=
    restrictedRepresentedChartPullbackArrow_value F i M e T β
  have hcomm (V : Over S) (z : V ⟶ L) :
      α.app (.op V) (z ≫ a) = β.app (.op V) (z ≫ r) :=
    (yonedaNat_precomp α z a).trans
      ((congrArg (F.map z.op) hvalue).trans (yonedaNat_precomp β z r).symm)
  refine ⟨L, yoneda.map a, r, ?_, SubterminalRelativeChart.baseChartProjection_open i T⟩
  apply IsPullback.of_forall_isPullback_app
  intro V
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    exact hcomm V.unop z
  · intro x y hxy
    exact (cancel_mono r).mp hxy.2
  · intro x y hxy
    let z := SubterminalRelativeChart.baseChartTestLift i T M x y
    have hz : z ≫ r = y := SubterminalRelativeChart.baseChartTestLift_projection i T M x y
    refine ⟨z, ?_, hz⟩
    apply restrictedRepresentedChartMap_injective F i M e V.unop
    exact (hcomm V.unop z).trans
      ((congrArg (β.app V) hz).trans hxy.symm)

theorem generalRestrictedRepresentedCharts_locallySurjective
    {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (U : S.OpenCover.{u})
    (M : ∀ a, Over (U.X a))
    (e : ∀ a, (Over.map (U.f a)).op ⋙ F ≅ yoneda.obj (M a)) :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Sigma.desc (fun a => SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F (U.f a) (M a) (e a))) := by
  constructor
  intro T s
  let V := fun a => SubterminalRelativeChart.baseChartTest (U.f a) T
  let r := fun a => SubterminalRelativeChart.baseChartProjection (U.f a) T
  have hcover : Sieve.ofArrows V r ∈ (Scheme.zariskiTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Scheme.Cover.mem_grothendieckTopology (U.pullback₁ T.hom)
  apply (Scheme.zariskiTopology.over S).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro W f ⟨a⟩
  let m := SubterminalOpenChartRepresentation.restrictedRepresentedChartPullbackArrow F (U.f a) (M a) (e a)
    T (yonedaEquiv.symm s)
  refine ⟨(Sigma.ι (fun a => yoneda.obj ((Over.map (U.f a)).obj (M a))) a).app
    (.op (V a)) m, ?_⟩
  have hι := congrArg
    (fun z : yoneda.obj ((Over.map (U.f a)).obj (M a)) ⟶ F => z.app (.op (V a)) m)
    (Sigma.ι_comp_desc (fun a => SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F (U.f a) (M a) (e a)) a)
  exact hι.trans (restrictedRepresentedChartPullbackArrow_value
    F (U.f a) (M a) (e a) T (yonedaEquiv.symm s))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneralRestrictedRepresentedCharts
