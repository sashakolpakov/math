import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Parameter Pullback Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual line bundles commute with canonical single/iterated parameter
pullback comparisons, including the group-preserving composition iso. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (X : Over S) (L : Line.Bundles.LineBundle X.left) {U T : Over S} (f : U ⟶ T)

def Line.Bundles.LineBundle.parameterDoublePullbackIso :
    (((L.pullback (pullback.fst X.hom T.hom)).pullback
      (pullback.fst ((Over.pullback T.hom).obj X).hom f.left)).pullback
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f X).hom.left).sheaf ≅
      (L.pullback (pullback.fst X.hom U.hom)).sheaf :=
  (Scheme.Modules.pullbackComp (Single.ParameterBaseChange.singleParameterBaseChangeIso f X).hom.left
    (pullback.fst ((Over.pullback T.hom).obj X).hom f.left)).app
      (L.pullback (pullback.fst X.hom T.hom)).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst f X)).app
      (L.pullback (pullback.fst X.hom T.hom)).sheaf ≪≫
    (Scheme.Modules.pullbackComp (Single.ParameterBaseChange.singleParameterBaseChangeMap f X) (pullback.fst X.hom T.hom)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp f X)).app L.sheaf

def Line.Bundles.LineBundle.parameterInversePullbackIso :
    ((L.pullback (pullback.fst X.hom U.hom)).pullback
      (Single.ParameterBaseChange.singleParameterBaseChangeIso f X).inv.left).sheaf ≅
        ((L.pullback (pullback.fst X.hom T.hom)).pullback
          (pullback.fst ((Over.pullback T.hom).obj X).hom f.left)).sheaf :=
  (Scheme.Modules.pullbackComp (Single.ParameterBaseChange.singleParameterBaseChangeIso f X).inv.left
    (pullback.fst X.hom U.hom)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst f X)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst ((Over.pullback T.hom).obj X).hom f.left)
        (pullback.fst X.hom T.hom)).symm.app L.sheaf

variable {B C : Scheme.{u}} [GrpObj X] (b : B ⟶ S) (c : C ⟶ B)

theorem LineBundle.ParameterPullbackCoherence.groupPullbackCompIso_hom_eq :
    (GroupPullbackComposition.groupPullbackCompIso X b c).hom = (Over.pullbackComp c b).hom.app X := by
  change (Over.pullbackComp c b).hom.app X ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem LineBundle.ParameterPullbackCoherence.groupPullbackCompIso_inv_original_fst :
    (GroupPullbackComposition.groupPullbackCompIso X b c).inv.left ≫ pullback.fst X.hom (c ≫ b) =
      pullback.fst ((Over.pullback b).obj X).hom c ≫ pullback.fst X.hom b := by
  apply ((((Over.forget C).mapIso (GroupPullbackComposition.groupPullbackCompIso X b c)).inv_comp_eq).mpr)
  change pullback.fst X.hom (c ≫ b) = (GroupPullbackComposition.groupPullbackCompIso X b c).hom.left ≫
    pullback.fst ((Over.pullback b).obj X).hom c ≫ pullback.fst X.hom b
  rw [LineBundle.ParameterPullbackCoherence.groupPullbackCompIso_hom_eq]
  exact (Pullback.Comparisons.pullbackComp_hom_fst_fst X b c).symm

def Line.Bundles.LineBundle.groupCompositionInversePullbackIso :
    ((L.pullback (pullback.fst X.hom (c ≫ b))).pullback
      (GroupPullbackComposition.groupPullbackCompIso X b c).inv.left).sheaf ≅
        ((L.pullback (pullback.fst X.hom b)).pullback
          (pullback.fst ((Over.pullback b).obj X).hom c)).sheaf :=
  (Scheme.Modules.pullbackComp (GroupPullbackComposition.groupPullbackCompIso X b c).inv.left
    (pullback.fst X.hom (c ≫ b))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (LineBundle.ParameterPullbackCoherence.groupPullbackCompIso_inv_original_fst X b c)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst ((Over.pullback b).obj X).hom c)
        (pullback.fst X.hom b)).symm.app L.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
