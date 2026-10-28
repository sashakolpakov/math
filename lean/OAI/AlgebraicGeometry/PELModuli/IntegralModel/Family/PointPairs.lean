import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Point Pairs -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointPairs

noncomputable section

/-! Lift a pair of actual family points to the product of the two
pulled-back families, preserving the Poincare projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace FamilyPointTransport
variable {S T : Scheme.{0}} (D A : Over S) (f : T ⟶ S) (p : Over.mk f ⟶ D ⊗ A)

def liftPair : T ⟶ ((Over.pullback f).obj D ⊗ (Over.pullback f).obj A).left :=
  pullback.lift (PointBaseChange.FamilyPointTransport.liftPoint D f (p ≫ fst D A).left (p ≫ fst D A).w)
    (PointBaseChange.FamilyPointTransport.liftPoint A f (p ≫ snd D A).left (p ≫ snd D A).w)
    ((PointBaseChange.FamilyPointTransport.liftPoint_snd _ _ _ _).trans (PointBaseChange.FamilyPointTransport.liftPoint_snd _ _ _ _).symm)

theorem liftPair_fst : liftPair D A f p ≫
    pullback.fst ((Over.pullback f).obj D).hom ((Over.pullback f).obj A).hom =
      PointBaseChange.FamilyPointTransport.liftPoint D f (p ≫ fst D A).left (p ≫ fst D A).w := pullback.lift_fst _ _ _

theorem liftPair_snd : liftPair D A f p ≫
    pullback.snd ((Over.pullback f).obj D).hom ((Over.pullback f).obj A).hom =
      PointBaseChange.FamilyPointTransport.liftPoint A f (p ≫ snd D A).left (p ≫ snd D A).w := pullback.lift_snd _ _ _

theorem liftPair_poincare {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : Over.mk f ⟶ D.abelian.scheme ⊗ A.scheme) :
    liftPair D.abelian.scheme A.scheme f p ≫ AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D f = p.left := by
  have hb₁ : AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D f ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      pullback.fst ((Over.pullback f).obj D.abelian.scheme).hom ((Over.pullback f).obj A.scheme).hom ≫
        pullback.fst D.abelian.scheme.hom f := AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_fst D f
  have hb₂ : AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D f ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.snd ((Over.pullback f).obj D.abelian.scheme).hom ((Over.pullback f).obj A.scheme).hom ≫
        pullback.fst A.scheme.hom f := AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_snd D f
  apply Over.tensorObj_ext
  · rw [Category.assoc, hb₁, ← Category.assoc, liftPair_fst, PointBaseChange.FamilyPointTransport.liftPoint_fst]
    rfl
  · rw [Category.assoc, hb₂, ← Category.assoc, liftPair_snd, PointBaseChange.FamilyPointTransport.liftPoint_fst]
    rfl

theorem liftPair_transport_poincare {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (h : T ⟶ S) (p : Over.mk f ⟶ D.abelian.scheme ⊗ A.scheme)
    (q : Over.mk h ⟶ D.abelian.scheme ⊗ A.scheme)
    (ed : (Over.pullback f).obj D.abelian.scheme ≅ (Over.pullback h).obj D.abelian.scheme)
    (ea : (Over.pullback f).obj A.scheme ≅ (Over.pullback h).obj A.scheme)
    (hd : PointBaseChange.FamilyPointTransport.transport D.abelian.scheme f h ed (p ≫ fst _ _).left (p ≫ fst _ _).w =
      (q ≫ fst _ _).left)
    (ha : PointBaseChange.FamilyPointTransport.transport A.scheme f h ea (p ≫ snd _ _).left (p ≫ snd _ _).w =
      (q ≫ snd _ _).left) :
    liftPair D.abelian.scheme A.scheme f p ≫ (ed.hom ⊗ₘ ea.hom).left ≫
      AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D h = q.left := by
  have hb₁ : AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D h ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      pullback.fst ((Over.pullback h).obj D.abelian.scheme).hom ((Over.pullback h).obj A.scheme).hom ≫
        pullback.fst D.abelian.scheme.hom h := AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_fst D h
  have hb₂ : AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D h ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.snd ((Over.pullback h).obj D.abelian.scheme).hom ((Over.pullback h).obj A.scheme).hom ≫
        pullback.fst A.scheme.hom h := AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_snd D h
  have he₁ : (ed.hom ⊗ₘ ea.hom).left ≫
      pullback.fst ((Over.pullback h).obj D.abelian.scheme).hom ((Over.pullback h).obj A.scheme).hom =
        pullback.fst ((Over.pullback f).obj D.abelian.scheme).hom ((Over.pullback f).obj A.scheme).hom ≫
          ed.hom.left := Over.tensorHom_left_fst _ _ _ _
  have he₂ : (ed.hom ⊗ₘ ea.hom).left ≫
      pullback.snd ((Over.pullback h).obj D.abelian.scheme).hom ((Over.pullback h).obj A.scheme).hom =
        pullback.snd ((Over.pullback f).obj D.abelian.scheme).hom ((Over.pullback f).obj A.scheme).hom ≫
          ea.hom.left := Over.tensorHom_left_snd _ _ _ _
  apply Over.tensorObj_ext
  · rw [Category.assoc, Category.assoc, hb₁,
      ← Category.assoc (ed.hom ⊗ₘ ea.hom).left, he₁]
    simp only [Category.assoc]
    rw [← Category.assoc (liftPair D.abelian.scheme A.scheme f p), liftPair_fst]
    exact hd
  · rw [Category.assoc, Category.assoc, hb₂,
      ← Category.assoc (ed.hom ⊗ₘ ea.hom).left, he₂]
    simp only [Category.assoc]
    rw [← Category.assoc (liftPair D.abelian.scheme A.scheme f p), liftPair_snd]
    exact ha

end FamilyPointTransport

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointPairs
