import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SheafBaseChangeConservative

/-! # Level Map Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelMapPullback

noncomputable section

/-! Native pullback and fppf detection of a full-level map, with literal
recovery on the constant labelled sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {g N : ℕ} {S T : Scheme.{0}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S)

def fullLevelMapPullback
    (α : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T ⟶ (A.pullback u).torsionFunctor N :=
  Functor.whiskerLeft (Over.map u).op α ≫ (A.torsionBaseChangeIso u N).inv

theorem fullLevelMapPullback_const_fst
    (α : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    ((fullLevelMapPullback A u α).app (.op (Over.mk (𝟙 T))) (LocallyConstant.const T c)).val.left ≫
      pullback.fst A.scheme.hom u =
      u ≫ (α.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val.left := by
  let V : Over T := Over.mk (𝟙 T)
  let k : (Over.map u).obj V ⟶ Over.mk (𝟙 S) := Over.homMk u (by simp [V])
  have hp := congrArg (fun x => x.val.left)
    ((A.torsionBaseChangeEquiv u V N).apply_symm_apply
      (α.app (.op ((Over.map u).obj V)) (LocallyConstant.const T c)))
  have hn := congrArg (fun x => x.val.left)
    (NatTrans.naturality_apply α k.op (LocallyConstant.const S c))
  exact hp.trans hn

theorem fullLevelMapPullback_eq
    (α : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N)
    (β : (A.pullback u).FullLevel N)
    (hc : ∀ c : Multiplicative (Fin (2 * g) → ZMod N),
      u ≫ (α.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val.left =
        (β.hom.app (.op (Over.mk (𝟙 T))) (LocallyConstant.const T c)).val.left ≫
          pullback.fst A.scheme.hom u) : fullLevelMapPullback A u α = β.hom := by
  apply AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.torsionNatTrans_ext_on_constants
  intro c
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (fullLevelMapPullback_const_fst A u α c).trans (hc c)
  · exact ((fullLevelMapPullback A u α).app (.op (Over.mk (𝟙 T)))
      (LocallyConstant.const T c)).val.w.trans
        (β.hom.app (.op (Over.mk (𝟙 T))) (LocallyConstant.const T c)).val.w.symm

theorem fullLevelMap_isIso_of_pullback [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (α : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N)
    [IsIso (fullLevelMapPullback A u α)] : IsIso α := by
  have : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⋙ forget GrpCat).IsRepresentable :=
    (AbelianModuli.HilbertConstruction.Level.Scheme.constantFullLevelRepresentable g N S).isRepresentable
  have : (A.torsionFunctor N ⋙ forget GrpCat).IsRepresentable := (A.torsionRepresentable N).isRepresentable
  have he : Functor.whiskerLeft (Over.map u).op α =
      fullLevelMapPullback A u α ≫ (A.torsionBaseChangeIso u N).hom := by
    simp only [fullLevelMapPullback, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsIso (Functor.whiskerLeft (Over.map u).op α) := by rw [he]; infer_instance
  exact Group.SheafBaseChangeConservative.groupFunctor_isIso_of_fppf_restriction u α

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelMapPullback
