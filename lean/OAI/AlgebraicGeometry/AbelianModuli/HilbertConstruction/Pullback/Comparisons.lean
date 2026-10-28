import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Comparisons -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric projection formulas for the canonical base-change comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' S'' : Scheme.{u}}

@[simp]
theorem Abelian.Schemes.AbelianScheme.pullbackCompIso_hom (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.pullbackCompIso f h).hom = (Over.pullbackComp h f).hom.app A.scheme := by
  change (Over.pullbackComp h f).hom.app A.scheme ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp]
theorem Abelian.Schemes.AbelianScheme.pullbackCompIso_inv (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.pullbackCompIso f h).inv = (Over.pullbackComp h f).inv.app A.scheme := by
  change 𝟙 _ ≫ (Over.pullbackComp h f).inv.app A.scheme = _
  exact Category.id_comp _

/-- The composition comparison commutes with projection to the original family. -/
theorem Pullback.Comparisons.pullbackComp_hom_fst_fst (X : Over S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    ((Over.pullbackComp h f).hom.app X).left ≫
        pullback.fst (pullback.snd X.hom f) h ≫ pullback.fst X.hom f =
      pullback.fst X.hom (h ≫ f) := by
  have w := conjugateEquiv_counit (Over.mapPullbackAdj (h ≫ f))
    ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj f)) (Over.mapComp h f).inv X
  have w' := congrArg (fun a => a.left) w
  change ((Over.pullbackComp h f).hom.app X).left ≫
      (pullback.fst (pullback.snd X.hom f) h ≫ pullback.fst X.hom f) =
    𝟙 _ ≫ pullback.fst X.hom (h ≫ f) at w'
  exact w'.trans (Category.id_comp _)

/-- The inverse abelian comparison identifies the projection from an iterated base change. -/
@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.pullbackCompIso_inv_left_fst (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.pullbackCompIso f h).inv.left ≫ pullback.fst A.scheme.hom (h ≫ f) =
      pullback.fst (A.pullback f).scheme.hom h ≫ pullback.fst A.scheme.hom f := by
  rw [Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  exact (((Over.forget S'').mapIso ((Over.pullbackComp h f).app A.scheme)).inv_comp_eq).mpr
    (Pullback.Comparisons.pullbackComp_hom_fst_fst A.scheme f h).symm

/-- Projection formula for a morphism between pulled-back families. -/
@[reassoc (attr := simp)]
theorem Pullback.Comparisons.overPullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) (f : S' ⟶ S) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

/-- First projection of the Poincare bundle's pullback map. -/
theorem Dual.Data.DualAbelianData.poincarePullbackOverMap_left_fst {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst D.abelian.scheme.hom f := by
  have w := congrArg (fun a => a.left) (D.poincarePullbackOverMap_fst f)
  change (D.poincarePullbackOverMap f).left ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
    pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
      (𝟙 _ ≫ pullback.fst D.abelian.scheme.hom f) at w
  exact w.trans (congrArg (fun a =>
    pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫ a)
      (Category.id_comp _))

/-- Second projection of the Poincare bundle's pullback map. -/
theorem Dual.Data.DualAbelianData.poincarePullbackOverMap_left_snd {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.snd (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst A.scheme.hom f :=
  congrArg (fun a => a.left) (D.poincarePullbackOverMap_snd f)

/-- The Poincare pullback map agrees with the monoidal base-change comparison. -/
theorem Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (f : S' ⟶ S) :
    PolarizationData.poincareBaseChangeMap D f = (D.poincarePullbackOverMap f).left := by
  apply Over.tensorObj_ext
  · exact (Category.assoc _ _ _).trans
      ((Over.μ_pullback_left_fst_fst (f := f) D.abelian.scheme A.scheme).trans
        (D.poincarePullbackOverMap_left_fst f).symm)
  · exact (Category.assoc _ _ _).trans
      ((Over.μ_pullback_left_fst_snd (f := f) D.abelian.scheme A.scheme).trans
        (D.poincarePullbackOverMap_left_snd f).symm)

@[reassoc (attr := simp)]
theorem Pullback.Comparisons.poincareBaseChangeMap_fst {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (f : S' ⟶ S) :
    PolarizationData.poincareBaseChangeMap D f ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst D.abelian.scheme.hom f :=
  (congrArg (fun a => a ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom)
    (Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D f)).trans
      (D.poincarePullbackOverMap_left_fst f)

@[reassoc (attr := simp)]
theorem Pullback.Comparisons.poincareBaseChangeMap_snd {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (f : S' ⟶ S) :
    PolarizationData.poincareBaseChangeMap D f ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.snd (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst A.scheme.hom f :=
  (congrArg (fun a => a ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom)
    (Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D f)).trans
      (D.poincarePullbackOverMap_left_snd f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
