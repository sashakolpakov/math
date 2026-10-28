import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelIsomorphisms

/-! # Relative Level Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso

noncomputable section

/-! The canonical comparison from an iterated pure-family pullback
transports the prescribed level by the actual restriction operation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L S)

def purePullbackCongrIso {T : Scheme.{0}} (f h : T ⟶ S) (w : f = h) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback h) := by
  subst h
  exact HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl _

theorem purePullbackCongrIso_abelian {T : Scheme.{0}} (f h : T ⟶ S) (w : f = h) :
    (purePullbackCongrIso A f h w).abelian = A.abelian.pullbackCongrIso f h w := by
  subst h
  rfl

def pureRelativePullbackIso {T U : Over S} (j : T ⟶ U) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback U.hom).pullback j.left) (A.pullback T.hom) :=
  (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A U.hom j.left).trans
    (purePullbackCongrIso A (j.left ≫ U.hom) T.hom j.w)

instance pureRelativePullbackIso_isMonHom {T U : Over S} (j : T ⟶ U) :
    IsMonHom ((pureRelativePullbackIso A j).abelian.hom :
      ((A.abelian.pullback U.hom).pullback j.left).scheme ⟶
        (A.abelian.pullback T.hom).scheme) :=
  (pureRelativePullbackIso A j).abelianGroup

theorem pureRelativePullbackIso_level {T U : Over S} (j : T ⟶ U)
    (β : (A.abelian.pullback U.hom).FullLevel N) :
    @HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g N T.left
      ((A.abelian.pullback U.hom).pullback j.left) (A.abelian.pullback T.hom)
      (β.pullback j.left) (pureRelativePullbackIso A j).abelian
      (pureRelativePullbackIso_isMonHom A j) = β.restrict j := by
  have he : (pureRelativePullbackIso A j).abelian.hom =
      (A.abelian.pullbackCompIso U.hom j.left).inv ≫
        (A.abelian.pullbackCongrIso (j.left ≫ U.hom) T.hom j.w).hom := by
    change (A.abelian.pullbackCompIso U.hom j.left).inv ≫
      (purePullbackCongrIso A (j.left ≫ U.hom) T.hom j.w).abelian.hom = _
    rw [purePullbackCongrIso_abelian]
    rfl
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V c
  change ((β.pullback j.left).hom.app (.op V) c).val ≫ (pureRelativePullbackIso A j).abelian.hom =
    (((β.pullback j.left).hom.app (.op V) c).val ≫
      (A.abelian.pullbackCompIso U.hom j.left).inv) ≫
        (A.abelian.pullbackCongrIso (j.left ≫ U.hom) T.hom j.w).hom
  rw [he, Category.assoc]
  rfl

def relativeAddedLevel (U : Over S) (β : (A.abelian.pullback U.hom).FullLevel N) :
    Level.Data.AddedFullLevel g δ L N U.left where
  auxiliary := A.pullback U.hom
  prescribed := β

def relativeAddedLevelIso {T U : Over S} (j : T ⟶ U)
    (β : (A.abelian.pullback U.hom).FullLevel N) :
    Level.Data.AddedFullLevel.Iso ((relativeAddedLevel A U β).pullback j.left)
      (relativeAddedLevel A T (β.restrict j)) where
  auxiliary := pureRelativePullbackIso A j
  prescribed := pureRelativePullbackIso_level A j β

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso
