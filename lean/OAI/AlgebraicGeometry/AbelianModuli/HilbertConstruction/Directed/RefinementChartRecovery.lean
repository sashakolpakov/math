import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterBaseChange

/-! # Refinement Chart Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RefinementChartRecovery

noncomputable section

/-! Recover a whole original chart from the literal maps on its directed
affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

section Member
variable {X : Scheme.{u}} (C : X.OpenCover) (j : C.I₀)

def directedRefinementMemberHom
    {v w : (C.X j).directedAffineCover.I₀} (h : v ⟶ w) :
    @Quiver.Hom (OpenRefinement.directedOpenRefinement C).I₀ inferInstance ⟨j, v⟩ ⟨j, w⟩ := by
  apply homOfLE
  let : IsOpenImmersion ((OpenRefinement.directedOpenRefinement C).f ⟨j, v⟩) :=
    (OpenRefinement.directedOpenRefinement C).map_prop ⟨j, v⟩
  let : IsOpenImmersion ((OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩) :=
    (OpenRefinement.directedOpenRefinement C).map_prop ⟨j, w⟩
  change ((OpenRefinement.directedOpenRefinement C).f ⟨j, v⟩).opensRange ≤
    ((OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩).opensRange
  have he : (C.X j).directedAffineCover.trans h ≫
      (OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩ = (OpenRefinement.directedOpenRefinement C).f ⟨j, v⟩ := by
    change (C.X j).directedAffineCover.trans h ≫
      ((C.X j).directedAffineCover.f w ≫ C.f j) = (C.X j).directedAffineCover.f v ≫ C.f j
    rw [← Category.assoc, Scheme.Cover.trans_map]
  rintro _ ⟨z, rfl⟩
  refine ⟨(C.X j).directedAffineCover.trans h z, ?_⟩
  exact congrArg (fun q : (C.X j).directedAffineCover.X v ⟶ X => q z) he

def directedRefinementMemberFunctor :
    (C.X j).directedAffineCover.I₀ ⥤ (OpenRefinement.directedOpenRefinement C).I₀ where
  obj v := ⟨j, v⟩
  map h := directedRefinementMemberHom C j h
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem directedRefinementMemberHom_trans
    {v w : (C.X j).directedAffineCover.I₀} (h : v ⟶ w) :
    (OpenRefinement.directedOpenRefinement C).trans (directedRefinementMemberHom C j h) =
      (C.X j).directedAffineCover.trans h := by
  let : IsOpenImmersion ((OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩) :=
    (OpenRefinement.directedOpenRefinement C).map_prop ⟨j, w⟩
  apply (cancel_mono ((OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩)).mp
  have he : (C.X j).directedAffineCover.trans h ≫ (OpenRefinement.directedOpenRefinement C).f ⟨j, w⟩ =
      (OpenRefinement.directedOpenRefinement C).f ⟨j, v⟩ :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ C.f j) ((C.X j).directedAffineCover.trans_map h))
  exact ((OpenRefinement.directedOpenRefinement C).trans_map (directedRefinementMemberHom C j h)).trans he.symm

theorem directedRefinementMemberHom_toMember
    {v w : (C.X j).directedAffineCover.I₀} (h : v ⟶ w) :
    (OpenRefinement.directedOpenRefinement C).trans (directedRefinementMemberHom C j h) ≫
        OpenRefinement.directedOpenRefinement_toMember C ⟨j, w⟩ = OpenRefinement.directedOpenRefinement_toMember C ⟨j, v⟩ := by
  rw [directedRefinementMemberHom_trans]
  exact (C.X j).directedAffineCover.trans_map h
end Member

abbrev parameterFamilyPullbackCover {S : Scheme.{u}} (A : Over S) (C : S.OpenCover) :
    A.left.OpenCover := C.pullback₁ A.hom

theorem singleParameterBaseChangeMap_eq_coverTransition
    {S : Scheme.{u}} (A : Over S) (C : S.OpenCover) [Category C.I₀] [C.LocallyDirected]
    {v w : C.I₀} (f : v ⟶ w) :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
      (Over.homMk (C.trans f) (C.trans_map f) : Over.mk (C.f v) ⟶ Over.mk (C.f w)) A =
        (parameterFamilyPullbackCover A C).trans f := by
  let : IsOpenImmersion ((parameterFamilyPullbackCover A C).f w) :=
    (parameterFamilyPullbackCover A C).map_prop w
  apply (cancel_mono ((parameterFamilyPullbackCover A C).f w)).mp
  exact (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp _ A).trans
    ((parameterFamilyPullbackCover A C).trans_map f).symm

variable {U X S : Scheme.{u}} (Y : Over U) (V : U.OpenCover)
variable [Category V.I₀] [V.LocallyDirected]
variable (q : ∀ i, (parameterFamilyPullbackCover Y V).X i ⟶ X)
variable (hq : ∀ {i j : V.I₀} (h : i ⟶ j), (parameterFamilyPullbackCover Y V).trans h ≫ q j = q i)

def wholeChartRecoveryMap : Y.left ⟶ X :=
  (parameterFamilyPullbackCover Y V).glueMorphismsOfLocallyDirected q hq

@[reassoc]
theorem wholeChartRecoveryMap_on_open (i : V.I₀) :
    (parameterFamilyPullbackCover Y V).f i ≫ wholeChartRecoveryMap Y V q hq = q i :=
  (parameterFamilyPullbackCover Y V).map_glueMorphismsOfLocallyDirected q hq i

variable (b : U ⟶ S) (p : X ⟶ S)
variable (H : ∀ i, IsPullback (V.pullbackHom Y.hom i) (q i) (V.f i ≫ b) p)

include H in
theorem wholeChartRecoveryMap_isPullback :
    IsPullback (wholeChartRecoveryMap Y V q hq) Y.hom p b := by
  have h : IsPullback Y.hom (wholeChartRecoveryMap Y V q hq) b p := by
    apply Scheme.isPullback_of_openCover Y.hom (wholeChartRecoveryMap Y V q hq) b p V
    intro i
    rw [wholeChartRecoveryMap_on_open]
    exact H i
  exact h.flip

def wholeChartRecoveryIso : Y ≅ (Over.pullback b).obj (Over.mk p) :=
  Over.isoMk (wholeChartRecoveryMap_isPullback Y V q hq b p H).isoPullback
    (wholeChartRecoveryMap_isPullback Y V q hq b p H).isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RefinementChartRecovery
