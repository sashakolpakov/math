import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.LevelReplacement

/-! # Relabel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

/-! Relabel only the auxiliary marking of the actual integral PEL
family. The prescribed marking, group schemes and integral action remain
the same, including over disconnected bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T U : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.relabelAuxiliary (A : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    PELId.IntegralAddedPELLevel P R iotaO L N T :=
  PELId.IntegralAddedPELLevel.ofPrescribed A.forgetAuxiliary (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel A.auxiliary.data.polarized.level b)

theorem PELId.IntegralAddedPELLevel.relabelAuxiliary_one (A : PELId.IntegralAddedPELLevel P R iotaO L N T) :
    A.relabelAuxiliary 1 = A :=
  congrArg (PELId.IntegralAddedPELLevel.ofPrescribed A.forgetAuxiliary) (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_one A.auxiliary.data.polarized.level)

theorem PELId.IntegralAddedPELLevel.relabelAuxiliary_mul (A : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (b c : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    (A.relabelAuxiliary b).relabelAuxiliary c = A.relabelAuxiliary (b * c) :=
  congrArg (PELId.IntegralAddedPELLevel.ofPrescribed A.forgetAuxiliary)
    (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_mul A.auxiliary.data.polarized.level b c)

theorem PELId.IntegralAddedPELLevel.relabelAuxiliary_pullback (A : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) (f : U ⟶ T) :
    (A.relabelAuxiliary b).pullback f =
      (A.pullback f).relabelAuxiliary (b.comap ⟨f.left, f.left.continuous⟩) :=
  congrArg (PELId.IntegralAddedPELLevel.ofPrescribed (A.forgetAuxiliary.pullback f))
    (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_pullback A.auxiliary.data.polarized.level b f.left)

theorem PELId.IntegralAddedPELLevel.relabelAuxiliary_forget (A : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    (A.relabelAuxiliary b).forgetAuxiliary = A.forgetAuxiliary := rfl

def PELId.IntegralAddedPELLevel.Iso.relabelAuxiliary {A B : PELId.IntegralAddedPELLevel P R iotaO L N T} (e : PELId.IntegralAddedPELLevel.Iso A B)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    PELId.IntegralAddedPELLevel.Iso (A.relabelAuxiliary b) (B.relabelAuxiliary b) where
  auxiliary := e.auxiliary.withLevel
    (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel A.auxiliary.data.polarized.level b)
    (AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel B.auxiliary.data.polarized.level b) (by
      apply AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_transport_eq
      apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
      exact e.auxiliary.polarized.level)
  prescribed := e.prescribed

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
