import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.Transport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelRelabeling

/-! # PEL Id -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

/-! The integral two-level PEL problem retains both actual ordered
markings on the same polarized abelian scheme and integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T U : Over (Spec (.of R))}

structure IntegralAddedPELLevel (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (R : Type) [CommRing R]
    (iotaO : NumberField.RingOfIntegers E →+* R) (L N : ℕ) (T : Over (Spec (.of R))) where
  auxiliary : PEL.Has.IntegralPELObject P R iotaO L T
  prescribed : auxiliary.data.polarized.abelian.FullLevel N

namespace IntegralAddedPELLevel

def pure (A : IntegralAddedPELLevel P R iotaO L N T) :
    AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N T.left :=
  ⟨A.auxiliary.data.polarized, A.prescribed⟩

def forgetAuxiliary (A : IntegralAddedPELLevel P R iotaO L N T) : PEL.Has.IntegralPELObject P R iotaO N T where
  data := { polarized := A.pure.forgetAuxiliary, action := A.auxiliary.data.action }
  rosati := A.auxiliary.rosati
  lieRanks := A.auxiliary.lieRanks

def ofPrescribed (A : PEL.Has.IntegralPELObject P R iotaO N T)
    (α : A.data.polarized.abelian.FullLevel L) : IntegralAddedPELLevel P R iotaO L N T where
  auxiliary := {
    data := { polarized := { A.data.polarized with level := α }, action := A.data.action }
    rosati := A.rosati
    lieRanks := A.lieRanks }
  prescribed := A.data.polarized.level

def pullback (A : IntegralAddedPELLevel P R iotaO L N T) (f : U ⟶ T) :
    IntegralAddedPELLevel P R iotaO L N U where
  auxiliary := A.auxiliary.pullback f
  prescribed := A.prescribed.pullback f.left

@[simp] theorem forget_ofPrescribed (A : PEL.Has.IntegralPELObject P R iotaO N T)
    (α : A.data.polarized.abelian.FullLevel L) : (ofPrescribed A α).forgetAuxiliary = A := rfl

theorem pullback_forget (A : IntegralAddedPELLevel P R iotaO L N T) (f : U ⟶ T) :
    (A.pullback f).forgetAuxiliary = A.forgetAuxiliary.pullback f := rfl

structure Iso (A B : IntegralAddedPELLevel P R iotaO L N T) where
  auxiliary : PEL.Iso.PolarizedActionIso A.auxiliary.data B.auxiliary.data
  prescribed : A.prescribed.transport auxiliary.polarized.abelian = B.prescribed

def Iso.toPure {A B : IntegralAddedPELLevel P R iotaO L N T} (e : Iso A B) :
    AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso A.pure B.pure :=
  ⟨e.auxiliary.polarized, e.prescribed⟩

def Iso.forgetAuxiliary {A B : IntegralAddedPELLevel P R iotaO L N T} (e : Iso A B) :
    PEL.Iso.PolarizedActionIso A.forgetAuxiliary.data B.forgetAuxiliary.data where
  polarized := e.toPure.forgetAuxiliary
  action := e.auxiliary.action

end IntegralAddedPELLevel

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId.IntegralAddedPELLevel

/-! Isomorphism and pullback calculus for actual integral PEL families
with two ordered levels. Both markings are retained in every comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T U : Over (Spec (.of R))}

namespace Iso
variable {A B C : IntegralAddedPELLevel P R iotaO L N T}

def refl (A : IntegralAddedPELLevel P R iotaO L N T) : Iso A A where
  auxiliary := PEL.Iso.PolarizedActionIso.refl A.auxiliary.data
  prescribed := (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso.refl A.pure).prescribed

def trans (a : Iso A B) (b : Iso B C) : Iso A C where
  auxiliary := a.auxiliary.trans b.auxiliary
  prescribed := (a.toPure.trans b.toPure).prescribed

def symm (a : Iso A B) : Iso B A where
  auxiliary := a.auxiliary.symm
  prescribed := a.toPure.symm.prescribed

def pullback (a : Iso A B) (f : U ⟶ T) : Iso (A.pullback f) (B.pullback f) where
  auxiliary := a.auxiliary.pullback f.left
  prescribed := (a.toPure.pullback f.left).prescribed

end Iso

def pullbackIdIso (A : IntegralAddedPELLevel P R iotaO L N T) : Iso (A.pullback (𝟙 T)) A where
  auxiliary := PEL.Iso.PolarizedActionIso.pullbackId A.auxiliary.data
  prescribed := (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackIdIso A.pure).prescribed

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId.IntegralAddedPELLevel

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

/-! Equal coefficient embeddings give the same actual two-level PEL
data. Only the proof of the Lie-rank condition is transported. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO j : NumberField.RingOfIntegers E →+* R} {V : Over (Spec (.of R))}

def IntegralAddedPELLevel.changeEmbedding (U : IntegralAddedPELLevel P R iotaO L N V)
    (h : iotaO = j) : IntegralAddedPELLevel P R j L N V where
  auxiliary := {
    data := U.auxiliary.data
    rosati := U.auxiliary.rosati
    lieRanks := h ▸ U.auxiliary.lieRanks }
  prescribed := U.prescribed

theorem integralAddedPEL_fine_changeEmbedding (U : IntegralAddedPELLevel P R iotaO L N V)
    (h : iotaO = j)
    (hclass : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : IntegralAddedPELLevel P R iotaO L N T),
      ∃! f : T ⟶ V, Nonempty (IntegralAddedPELLevel.Iso (U.pullback f) A))
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : IntegralAddedPELLevel P R j L N T) :
    ∃! f : T ⟶ V, Nonempty (IntegralAddedPELLevel.Iso ((U.changeEmbedding h).pullback f) A) := by
  let A' := A.changeEmbedding h.symm
  obtain ⟨f, ⟨e⟩, hu⟩ := hclass T A'
  refine ⟨f, ⟨{ auxiliary := e.auxiliary, prescribed := e.prescribed }⟩, ?_⟩
  rintro g ⟨a⟩
  exact hu g ⟨{ auxiliary := a.auxiliary, prescribed := a.prescribed }⟩

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

end

end OAI
