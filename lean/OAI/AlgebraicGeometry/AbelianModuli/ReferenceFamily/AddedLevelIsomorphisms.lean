import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelFamilies

/-! # Added Level Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual isomorphisms and pullbacks for the two-level pure family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T V : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}

def Level.Data.AddedFullLevel.pullback (A : Level.Data.AddedFullLevel g δ L N S) (f : T ⟶ S) : Level.Data.AddedFullLevel g δ L N T where
  auxiliary := A.auxiliary.pullback f
  prescribed := A.prescribed.pullback f

structure Level.Data.AddedFullLevel.Iso (A B : Level.Data.AddedFullLevel g δ L N S) where
  auxiliary : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.auxiliary B.auxiliary
  prescribed : A.prescribed.transport auxiliary.abelian = B.prescribed

section

variable {A B C : Level.Data.AddedFullLevel g δ L N S}

def Level.Data.AddedFullLevel.Iso.refl (A : Level.Data.AddedFullLevel g δ L N S) : Level.Data.AddedFullLevel.Iso A A where
  auxiliary := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl A.auxiliary
  prescribed := Level.IsoCalculus.fullLevel_transport_refl A.prescribed

def Level.Data.AddedFullLevel.Iso.trans (a : Level.Data.AddedFullLevel.Iso A B) (b : Level.Data.AddedFullLevel.Iso B C) : Level.Data.AddedFullLevel.Iso A C where
  auxiliary := a.auxiliary.trans b.auxiliary
  prescribed := (Level.IsoCalculus.fullLevel_transport_trans A.prescribed a.auxiliary.abelian b.auxiliary.abelian).symm.trans
    ((congrArg (fun α => α.transport b.auxiliary.abelian) a.prescribed).trans b.prescribed)

def Level.Data.AddedFullLevel.Iso.symm (a : Level.Data.AddedFullLevel.Iso A B) : Level.Data.AddedFullLevel.Iso B A where
  auxiliary := a.auxiliary.symm
  prescribed := (congrArg (fun α => α.transport a.auxiliary.abelian.symm) a.prescribed).symm.trans
    (Level.IsoCalculus.fullLevel_transport_symm A.prescribed a.auxiliary.abelian)

def Level.Data.AddedFullLevel.Iso.pullback (a : Level.Data.AddedFullLevel.Iso A B) (f : T ⟶ S) : Level.Data.AddedFullLevel.Iso (A.pullback f) (B.pullback f) where
  auxiliary := a.auxiliary.pullback f
  prescribed := (Level.IsoCalculus.fullLevel_transport_pullback A.prescribed a.auxiliary.abelian f).symm.trans
    (congrArg (fun α => α.pullback f) a.prescribed)

theorem Level.Data.AddedFullLevel.Iso.prescribed_basis (a : Level.Data.AddedFullLevel.Iso A B) (U : Over S)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (A.prescribed.hom.app (.op U) c).val ≫ a.auxiliary.abelian.hom =
      (B.prescribed.hom.app (.op U) c).val :=
  congrArg (fun α : B.auxiliary.abelian.FullLevel N => (α.hom.app (.op U) c).val) a.prescribed

end

def Level.Data.AddedFullLevel.pullbackCompIso (A : Level.Data.AddedFullLevel g δ L N S) (f : T ⟶ S) (h : V ⟶ T) :
    Level.Data.AddedFullLevel.Iso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  auxiliary := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.auxiliary f h
  prescribed := A.prescribed.transport_pullbackComp f h

def Level.Data.AddedFullLevel.pullbackCongrIso (A : Level.Data.AddedFullLevel g δ L N S) (f h : T ⟶ S) (w : f = h) :
    Level.Data.AddedFullLevel.Iso (A.pullback f) (A.pullback h) := by
  subst h
  exact Level.Data.AddedFullLevel.Iso.refl _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
