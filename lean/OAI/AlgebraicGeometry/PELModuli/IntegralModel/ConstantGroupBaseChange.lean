import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange

/-! # Constant Group Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantGroupBaseChange

noncomputable section

/-! The constant-scheme cartesian comparison preserves the actual group
law. The proof lifts the natural group-valued point comparison through
fully faithful Yoneda, then identifies its underlying canonical map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace GroupPoints

def baseChangeGroupIso {S S' : Scheme} (H : Over S) [GrpObj H] (f : S' ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj H) ≅ (Over.map f).op ⋙ yonedaGrpObj H :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (IntegralModel.Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv H f T.unop)) (by
    intro T U h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _)

end GroupPoints

namespace ConstantGroupModels

variable {S S' : Scheme} (f : S' ⟶ S) (G : Type) [Group G]

def groupBaseChangeGrpIso : Grp.mk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S' G) ≅
    Grp.mk ((Over.pullback f).obj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G)) :=
  yonedaGrpFullyFaithful.preimageIso
    (ConstantBaseChange.ConstantGroupModels.pointIso S' G ≪≫
      (Functor.isoWhiskerLeft (Over.map f).op (ConstantBaseChange.ConstantGroupModels.pointIso S G)).symm ≪≫
        (GroupPoints.baseChangeGroupIso (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) f).symm)

def groupBaseChangeIso : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S' G ≅ (Over.pullback f).obj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) :=
  (Grp.forget (Over S')).mapIso (groupBaseChangeGrpIso f G)

instance groupBaseChangeIso_isMonHom : IsMonHom (groupBaseChangeIso f G).hom :=
  inferInstanceAs (IsMonHom (groupBaseChangeGrpIso f G).hom.hom.hom)

theorem groupBaseChangeIso_hom :
    (groupBaseChangeIso f G).hom = (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f G).hom := by
  rfl

instance canonicalBaseChangeIso_isMonHom : IsMonHom (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f G).hom := by
  rw [← groupBaseChangeIso_hom f G]
  infer_instance

end ConstantGroupModels

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantGroupBaseChange
