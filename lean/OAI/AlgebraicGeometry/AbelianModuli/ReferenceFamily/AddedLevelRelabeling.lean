import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelIsomorphisms

/-! # Added Level Relabeling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Change only the auxiliary ordered marking of an actual two-level
family, preserving its prescribed marking and polarized scheme data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}

def Level.Data.AddedFullLevel.Iso.forgetAuxiliary {A B : Level.Data.AddedFullLevel g δ L N S} (e : Level.Data.AddedFullLevel.Iso A B) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.forgetAuxiliary B.forgetAuxiliary where
  abelian := e.auxiliary.abelian
  dual := e.auxiliary.dual
  abelianGroup := e.auxiliary.abelianGroup
  dualGroup := e.auxiliary.dualGroup
  polarization := e.auxiliary.polarization
  poincare := e.auxiliary.poincare
  level := e.prescribed_basis

def Level.Data.AddedFullLevel.pullbackIdIso (A : Level.Data.AddedFullLevel g δ L N S) : Level.Data.AddedFullLevel.Iso (A.pullback (𝟙 S)) A where
  auxiliary := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.auxiliary
  prescribed := by
    apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    intro U c
    exact (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.forgetAuxiliary).level U c

variable [NeZero L]

def Level.Data.AddedFullLevel.relabelAuxiliary (A : Level.Data.AddedFullLevel g δ L N S)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)) : Level.Data.AddedFullLevel g δ L N S where
  auxiliary := { A.auxiliary with level := Level.IsoCalculus.relabelFullLevel A.auxiliary.level b }
  prescribed := A.prescribed

theorem Level.Data.AddedFullLevel.relabelAuxiliary_one (A : Level.Data.AddedFullLevel g δ L N S) :
    A.relabelAuxiliary 1 = A :=
  congrArg (fun α => (⟨{ A.auxiliary with level := α }, A.prescribed⟩ : Level.Data.AddedFullLevel g δ L N S))
    (Level.IsoCalculus.relabelFullLevel_one A.auxiliary.level)

theorem Level.Data.AddedFullLevel.relabelAuxiliary_mul (A : Level.Data.AddedFullLevel g δ L N S)
    (b c : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    (A.relabelAuxiliary b).relabelAuxiliary c = A.relabelAuxiliary (b * c) :=
  congrArg (fun α => (⟨{ A.auxiliary with level := α }, A.prescribed⟩ : Level.Data.AddedFullLevel g δ L N S))
    (Level.IsoCalculus.relabelFullLevel_mul A.auxiliary.level b c)

theorem Level.Data.AddedFullLevel.relabelAuxiliary_pullback (A : Level.Data.AddedFullLevel g δ L N S)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)) (f : T ⟶ S) :
    (A.relabelAuxiliary b).pullback f =
      (A.pullback f).relabelAuxiliary (b.comap ⟨f, f.continuous⟩) :=
  congrArg (fun α => (⟨{ (A.auxiliary.pullback f) with level := α }, A.prescribed.pullback f⟩ :
    Level.Data.AddedFullLevel g δ L N T)) (Level.IsoCalculus.relabelFullLevel_pullback A.auxiliary.level b f)

theorem Level.Data.AddedFullLevel.relabelAuxiliary_forget (A : Level.Data.AddedFullLevel g δ L N S)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    (A.relabelAuxiliary b).forgetAuxiliary = A.forgetAuxiliary := rfl

def Level.Data.AddedFullLevel.Iso.relabelAuxiliary {A B : Level.Data.AddedFullLevel g δ L N S} (e : Level.Data.AddedFullLevel.Iso A B)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    Level.Data.AddedFullLevel.Iso (A.relabelAuxiliary b) (B.relabelAuxiliary b) where
  auxiliary := {
    abelian := e.auxiliary.abelian
    dual := e.auxiliary.dual
    abelianGroup := e.auxiliary.abelianGroup
    dualGroup := e.auxiliary.dualGroup
    polarization := e.auxiliary.polarization
    poincare := e.auxiliary.poincare
    level := by
      have he : A.auxiliary.level.transport e.auxiliary.abelian = B.auxiliary.level := by
        apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
        exact e.auxiliary.level
      have h := Level.IsoCalculus.relabelFullLevel_transport_eq A.auxiliary.level B.auxiliary.level b
        e.auxiliary.abelian he
      intro U c
      exact congrArg (fun α : B.auxiliary.abelian.FullLevel L => (α.hom.app (.op U) c).val) h }
  prescribed := e.prescribed

def Level.Data.AddedFullLevel.Iso.forgetRelabelPullback {A : Level.Data.AddedFullLevel g δ L N S}
    {f : S ⟶ S} {b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g L)}
    (e : Level.Data.AddedFullLevel.Iso (A.pullback f) (A.relabelAuxiliary b)) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.forgetAuxiliary.pullback f) A.forgetAuxiliary :=
  e.forgetAuxiliary

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
