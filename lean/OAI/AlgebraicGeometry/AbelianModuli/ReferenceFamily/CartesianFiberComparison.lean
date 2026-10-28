import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Cartesian Fiber Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily

noncomputable section

section

/-! Actual cartesian tensor products of a family identification. These
give the covering map used to descend multiplication. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S T : Scheme.{0}} (u : T ⟶ S) (A : Over T) (B : Over S)
    (e : A ≅ (Over.pullback u).obj B)

def totalMap : A.left ⟶ B.left := e.hom.left ≫ pullback.fst B.hom u

theorem totalMap_base : totalMap u A B e ≫ B.hom = A.hom ≫ u :=
  (((Over.mapPullbackAdj u).homEquiv A B).symm e.hom).w

theorem totalMap_isPullback : IsPullback A.hom (totalMap u A B e) u B.hom :=
  (IsPullback.of_iso_pullback ⟨totalMap_base u A B e⟩
    ((Over.forget T).mapIso e) rfl e.hom.w).flip

def tensorComparison : A ⊗ A ≅ (Over.pullback u).obj (B ⊗ B) :=
  tensorIso e e ≪≫ Functor.Monoidal.μIso (Over.pullback u) B B

def tensorMap : (A ⊗ A).left ⟶ (B ⊗ B).left :=
  totalMap u (A ⊗ A) (B ⊗ B) (tensorComparison u A B e)

theorem tensorMap_isPullback : IsPullback (A ⊗ A).hom (tensorMap u A B e) u (B ⊗ B).hom :=
  totalMap_isPullback _ _ _ _

theorem tensorMap_eq : tensorMap u A B e =
    (e.hom ⊗ₘ e.hom).left ≫ Picard.PoincareBundle.Field.ProductBaseChange.productMap u B :=
  Category.assoc (e.hom ⊗ₘ e.hom).left
    (Functor.Monoidal.μIso (Over.pullback u) B B).hom.left (pullback.fst (B ⊗ B).hom u)

theorem tensorMap_fst : tensorMap u A B e ≫ (fst B B).left =
    (fst A A).left ≫ totalMap u A B e := by
  let m := (e.hom ⊗ₘ e.hom).left
  let p := Picard.PoincareBundle.Field.ProductBaseChange.productMap u B
  let r := pullback.fst B.hom u
  have he : m ≫ (fst ((Over.pullback u).obj B) ((Over.pullback u).obj B)).left =
      (fst A A).left ≫ e.hom.left := Over.tensorHom_left_fst _ _ _ _
  exact (congrArg (fun q => q ≫ (fst B B).left) (tensorMap_eq u A B e)).trans
    ((Category.assoc m p (fst B B).left).trans
      ((congrArg (fun q => m ≫ q) (Picard.PoincareBundle.Field.ProductBaseChange.first u B)).trans
        ((Category.assoc m (fst ((Over.pullback u).obj B) ((Over.pullback u).obj B)).left r).symm.trans
          ((congrArg (fun q => q ≫ r) he).trans
            (Category.assoc (fst A A).left e.hom.left r)))))

theorem tensorMap_snd : tensorMap u A B e ≫ (snd B B).left =
    (snd A A).left ≫ totalMap u A B e := by
  let m := (e.hom ⊗ₘ e.hom).left
  let p := Picard.PoincareBundle.Field.ProductBaseChange.productMap u B
  let r := pullback.fst B.hom u
  have he : m ≫ (snd ((Over.pullback u).obj B) ((Over.pullback u).obj B)).left =
      (snd A A).left ≫ e.hom.left := Over.tensorHom_left_snd _ _ _ _
  exact (congrArg (fun q => q ≫ (snd B B).left) (tensorMap_eq u A B e)).trans
    ((Category.assoc m p (snd B B).left).trans
      ((congrArg (fun q => m ≫ q) (Picard.PoincareBundle.Field.ProductBaseChange.second u B)).trans
        ((Category.assoc m (snd ((Over.pullback u).obj B) ((Over.pullback u).obj B)).left r).symm.trans
          ((congrArg (fun q => q ≫ r) he).trans
            (Category.assoc (snd A A).left e.hom.left r)))))

end

/-! A recovered family gives a native group isomorphism on each
geometric fiber, with its exact map back to the original total scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

variable {S Y T : Scheme.{0}} {g h : ℕ} (u : Y ⟶ S)
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (e : A.scheme ≅ (B.pullback u).scheme) (s : T ⟶ Y)

def fiberComparison : (A.pullback s).scheme ≅ (B.pullback (s ≫ u)).scheme :=
  (Over.pullback s).mapIso e ≪≫ (B.pullbackCompIso u s).symm

instance fiberComparison_isMonHom [IsMonHom e.hom] : IsMonHom (fiberComparison u A B e s).hom := by
  let : GrpObj ((Over.pullback s).obj A.scheme) := Functor.grpObjObj
  let : GrpObj ((Over.pullback s).obj (B.pullback u).scheme) := Functor.grpObjObj
  let a : (A.pullback s).scheme ⟶ ((B.pullback u).pullback s).scheme := (Over.pullback s).map e.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom ((Over.pullback s).map e.hom))
  have : IsMonHom (B.pullbackCompIso u s).inv := inferInstance
  exact instIsMonHomComp a (B.pullbackCompIso u s).inv

theorem fiberComparison_projection :
    (fiberComparison u A B e s).hom.left ≫ pullback.fst B.scheme.hom (s ≫ u) =
      pullback.fst A.scheme.hom s ≫ totalMap u A.scheme B.scheme e := by
  let k := ((Over.pullback s).map e.hom).left
  let c := (B.pullbackCompIso u s).inv.left
  let p := pullback.fst (B.pullback u).scheme.hom s
  let r := pullback.fst B.scheme.hom u
  have hc : c ≫ pullback.fst B.scheme.hom (s ≫ u) = p ≫ r := B.pullbackCompIso_inv_left_fst u s
  have hk : k ≫ p = pullback.fst A.scheme.hom s ≫ e.hom.left := HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst e.hom s
  exact (Category.assoc k c (pullback.fst B.scheme.hom (s ≫ u))).trans
    ((congrArg (fun f => k ≫ f) hc).trans
      ((Category.assoc k p r).symm.trans
        ((congrArg (fun f => f ≫ r) hk).trans (Category.assoc _ _ _))))

theorem totalMap_morphism_comparison {D : Over Y} {E : Over S}
    (eD : D ≅ (Over.pullback u).obj E) (p : A.scheme ⟶ D) (w : B.scheme ⟶ E)
    (hc : e.hom ≫ (Over.pullback u).map w = p ≫ eD.hom) :
    totalMap u A.scheme B.scheme e ≫ w.left = p.left ≫ totalMap u D E eD := by
  have hh := congrArg (fun f : A.scheme ⟶ (Over.pullback u).obj E => f.left ≫ pullback.fst E.hom u) hc
  have hw := HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst w u
  change (e.hom.left ≫ ((Over.pullback u).map w).left) ≫ pullback.fst E.hom u =
    (p.left ≫ eD.hom.left) ≫ pullback.fst E.hom u at hh
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => e.hom.left ≫ f) hw.symm).trans
      ((Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily
