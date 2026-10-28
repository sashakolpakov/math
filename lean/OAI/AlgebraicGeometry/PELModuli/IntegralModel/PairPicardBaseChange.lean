import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection

/-! # Pair Picard Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardBaseChange

noncomputable section

/-! A line on a dual-by-abelian product has the expected relative
Picard class after scalar base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {S T : Scheme.{u}} {g : ℕ} (A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : T ⟶ S)

theorem pairBaseChangeProjection_family :
    PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme =
      (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme b (D.pullback b).scheme).hom ≫
        (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b ▷ A.scheme).left := by
  apply Over.tensorObj_ext
  · change _ = ((A.baseChangeFamilyIso b (D.pullback b).scheme).hom ≫
        (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b ▷ A.scheme) ≫ fst D.scheme A.scheme).left
    rw [whiskerRight_fst, ← Category.assoc, A.baseChangeFamilyIso_hom_fst]
    erw [PairBaseChangeProjection.pairBaseChangeProjection_fst]
    simp only [Over.comp_left, Over.map_map_left, AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection,
      AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply, Over.id_left, Category.id_comp]
    rfl
  · change _ = ((A.baseChangeFamilyIso b (D.pullback b).scheme).hom ≫
        (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b ▷ A.scheme) ≫ snd D.scheme A.scheme).left
    rw [whiskerRight_snd, A.baseChangeFamilyIso_hom_snd]
    erw [PairBaseChangeProjection.pairBaseChangeProjection_snd]
    exact (A.baseChangePointsEquiv_apply b _ _).symm

theorem pairLinePullback_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.scheme ⊗ A.scheme).left) :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme b).hom.app (.op (D.pullback b).scheme)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b).op
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  let e := AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme b (D.pullback b).scheme
  let c := (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b ▷ A.scheme).left
  have hp : PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme = e.hom ≫ c :=
    pairBaseChangeProjection_family A D b
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [hp]
  exact (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.hom c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso e).left_inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardBaseChange
