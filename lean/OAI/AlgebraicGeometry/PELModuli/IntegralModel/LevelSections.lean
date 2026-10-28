import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Level Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelSections

noncomputable section

/-! The labelled sections of an actual full level and their literal
compatibility with family-point transport. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {g N : ℕ} {S T : Scheme.{0}} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

def fullLevelSection (level : A.FullLevel N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) : Over.mk (𝟙 S) ⟶ A.scheme :=
  (level.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val

theorem fullLevelSection_pullback_fst (level : A.FullLevel N) (f : T ⟶ S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (fullLevelSection (level.pullback f) c).left ≫ pullback.fst A.scheme.hom f =
      f ≫ (fullLevelSection level c).left := by
  let V : Over T := Over.mk (𝟙 T)
  let k : (Over.map f).obj V ⟶ Over.mk (𝟙 S) := Over.homMk f (by simp [V])
  have hn := NatTrans.naturality_apply level.hom k.op (LocallyConstant.const S c)
  have hp := congrArg Over.Hom.left (level.pullback_basis f V (LocallyConstant.const T c))
  have hn' := congrArg (fun x => x.val.left) hn
  exact hp.trans hn'

theorem fullLevelSection_liftPoint (level : A.FullLevel N) (f : T ⟶ S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Family.PointBaseChange.FamilyPointTransport.liftPoint A.scheme f (f ≫ (fullLevelSection level c).left)
      (by rw [Category.assoc, (fullLevelSection level c).w]; exact Category.comp_id f) =
      (fullLevelSection (level.pullback f) c).left := by
  apply pullback.hom_ext
  · exact (Family.PointBaseChange.FamilyPointTransport.liftPoint_fst _ _ _ _).trans
      (fullLevelSection_pullback_fst level f c).symm
  · exact (Family.PointBaseChange.FamilyPointTransport.liftPoint_snd _ _ _ _).trans
      (fullLevelSection (level.pullback f) c).w.symm

theorem fullLevelSection_transport (level : A.FullLevel N) (f h : T ⟶ S)
    (e : (A.pullback f).scheme ≅ (A.pullback h).scheme)
    (he : ∀ (V : Over T) (c : LocallyConstant V.left
      (Multiplicative (Fin (2 * g) → ZMod N))),
      ((level.pullback f).hom.app (.op V) c).val ≫ e.hom =
        ((level.pullback h).hom.app (.op V) c).val)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Family.PointBaseChange.FamilyPointTransport.transport A.scheme f h e (f ≫ (fullLevelSection level c).left)
      (by rw [Category.assoc, (fullLevelSection level c).w]; exact Category.comp_id f) =
      h ≫ (fullLevelSection level c).left := by
  unfold Family.PointBaseChange.FamilyPointTransport.transport
  rw [fullLevelSection_liftPoint, ← Category.assoc]
  have hc := congrArg Over.Hom.left (he (Over.mk (𝟙 T)) (LocallyConstant.const T c))
  exact (congrArg (fun k => k ≫ pullback.fst A.scheme.hom h) hc).trans
    (fullLevelSection_pullback_fst level h c)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelSections
