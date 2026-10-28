import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.FrameUniqueness

/-! # Frame Rigidity -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity
section

/-! Uniqueness of an actual frame classifying map after its underlying
prescribed-level PEL classifying map has been fixed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace IntegralPELFrame
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T : Over (Spec (.of R))}
    (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

def comparisonAt (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T) (j : T ⟶ FrameExistence.IntegralPELFrame.space U hL)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback j) A)
    (f : T ⟶ X) (h : j ≫ FrameExistence.IntegralPELFrame.forget U hL = f) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso
      (FrameExistence.IntegralPELFrame.relative U f ((Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL).restrict
        (Integral.PureAddedLevel.IntegralPureModel.addedMapFrame (FrameExistence.IntegralPELFrame.pureModel U) hL j f h))) A :=
  (FrameExistence.IntegralPELFrame.frameComparison U hL f (Integral.PureAddedLevel.IntegralPureModel.addedMapFrame (FrameExistence.IntegralPELFrame.pureModel U) hL j f h)).symm.trans a

theorem classifying_unique_fixed_base (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (f : T ⟶ X)
    (hRigid : ∀ e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.data.polarized.pullback f.left)
      (U.data.polarized.pullback f.left),
      e.abelian.hom = 𝟙 (U.data.polarized.abelian.pullback f.left).scheme)
    (j k : T ⟶ FrameExistence.IntegralPELFrame.space U hL) (hj : j ≫ FrameExistence.IntegralPELFrame.forget U hL = f) (hk : k ≫ FrameExistence.IntegralPELFrame.forget U hL = f)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback j) A)
    (b : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback k) A) : j = k := by
  let q := Integral.PureAddedLevel.IntegralPureModel.addedMapFrame (FrameExistence.IntegralPELFrame.pureModel U) hL j f hj
  let r := Integral.PureAddedLevel.IntegralPureModel.addedMapFrame (FrameExistence.IntegralPELFrame.pureModel U) hL k f hk
  have hβ := Prescribed.FrameUniqueness.prescribedPEL_frame_eq (U.pullback f) hRigid
    ((Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL).restrict q)
    ((Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL).restrict r) A
    (comparisonAt U hL A j a f hj) (comparisonAt U hL A k b f hk)
  have hq : q = r := (Integral.FrameFactorization.IntegralLevelCover.fullFramePointsEquiv U.data.polarized.abelian hL (Over.mk f.left)).injective hβ
  exact Over.OverMorphism.ext (congrArg (fun z => z.left) hq)

end IntegralPELFrame

end

/-! Rigidity of the prescribed-level family makes its frame cover a
fine parameter for PEL objects with both levels. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace IntegralPELFrame
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T : Over (Spec (.of R))}
    (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

theorem classifying_unique (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (hclass : ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.forgetAuxiliary.data))
    (hRigid : ∀ (f : T ⟶ X)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.data.polarized.pullback f.left) (U.data.polarized.pullback f.left)),
      e.abelian.hom = 𝟙 (U.data.polarized.abelian.pullback f.left).scheme)
    (j k : T ⟶ FrameExistence.IntegralPELFrame.space U hL)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback j) A)
    (b : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback k) A) : j = k := by
  let f := j ≫ FrameExistence.IntegralPELFrame.forget U hL
  let h := k ≫ FrameExistence.IntegralPELFrame.forget U hL
  let a' := comparisonAt U hL A j a f rfl
  let b' := comparisonAt U hL A k b h rfl
  obtain ⟨u, _, hu⟩ := hclass
  have hh : h = f := (hu h ⟨b'.forgetAuxiliary⟩).trans (hu f ⟨a'.forgetAuxiliary⟩).symm
  exact classifying_unique_fixed_base U hL A f (hRigid f) j k rfl hh a b

end IntegralPELFrame

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity

namespace AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity.IntegralPELFrame

/-! The reference frame cover is fine without a noetherian assumption
on its base once prescribed-level rigidity is proved for all families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

theorem isFine_of_family_rigidity
    (hclass : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    (hRigid : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P R iotaO N T)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.data.polarized A.data.polarized),
      e.abelian.hom = 𝟙 A.data.polarized.abelian.scheme)
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T) :
    ∃! j : T ⟶ FrameExistence.IntegralPELFrame.space U hL,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback j) A) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hclass T A.forgetAuxiliary
  obtain ⟨j, ⟨a⟩⟩ := FrameExistence.IntegralPELFrame.classifying_exists U hL A f e
  refine ⟨j, ⟨a⟩, ?_⟩
  rintro k ⟨b⟩
  exact classifying_unique U hL A (hclass T A.forgetAuxiliary)
    (fun f e => hRigid T (U.pullback f) e) k j b a

end AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity.IntegralPELFrame

end

end OAI
