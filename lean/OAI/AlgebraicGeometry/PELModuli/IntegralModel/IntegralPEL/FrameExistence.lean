import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Reconstruction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.RelativeFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel

/-! # Frame Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence

noncomputable section

section

/-! The actual auxiliary-frame family over a prescribed-level integral
PEL family. The comparison preserves the action and both markings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T : Over (Spec (.of R))}

namespace IntegralPELFrame
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel.IntegralPureModel
variable (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

def pureModel : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of R)) :=
  ⟨X, U.data.polarized⟩

abbrev space : Over (Spec (.of R)) := Integral.PureAddedLevel.IntegralPureModel.addedLevelSpace (pureModel U) hL (N := L)
abbrev forget : space U hL ⟶ X := Integral.PureAddedLevel.IntegralPureModel.addedLevelForget (pureModel U) hL

def universal : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N (space U hL) :=
  by
    apply IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed (U.pullback (forget U hL))
    change (U.data.polarized.abelian.pullback (forget U hL).left).FullLevel L
    exact Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL

def relative (f : T ⟶ X) (β : (U.data.polarized.abelian.pullback f.left).FullLevel L) :
    IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T := IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed (U.pullback f) β

def frameComparison (f : T ⟶ X)
    (q : Over.mk f.left ⟶ Integral.PureAddedLevel.IntegralPureModel.prescribedFrame (pureModel U) hL (N := L)) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso
      ((universal U hL).pullback (Integral.PureAddedLevel.IntegralPureModel.frameToAddedMap (pureModel U) hL f q))
      (relative U f ((Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL).restrict q)) :=
  RelativeFrame.integralRelativeFrameIso U (Integral.PureAddedLevel.IntegralPureModel.prescribedFrame (pureModel U) hL)
    (Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL) f q

end IntegralPELFrame

end

/-! A classifying map for the prescribed-level PEL family lifts to
the actual frame cover while retaining both ordered markings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace IntegralPELFrame
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PureAddedLevel.IntegralPureModel
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T : Over (Spec (.of R))}
    (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

theorem classifying_exists (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (f : T ⟶ X) (e : PEL.Iso.PolarizedActionIso (U.pullback f).data A.forgetAuxiliary.data) :
    ∃ j : T ⟶ space U hL,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((universal U hL).pullback j) A) := by
  let β : (U.data.polarized.abelian.pullback f.left).FullLevel L :=
    @AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport (3 * s) L T.left A.auxiliary.data.polarized.abelian
      (U.data.polarized.abelian.pullback f.left) A.auxiliary.data.polarized.level
      e.polarized.abelian.symm e.polarized.symm.abelianGroup
  let q : Over.mk f.left ⟶ Integral.PureAddedLevel.IntegralPureModel.prescribedFrame (pureModel U) hL (N := L) :=
    (Integral.FrameFactorization.IntegralLevelCover.fullFramePointsEquiv U.data.polarized.abelian hL (Over.mk f.left)).symm β
  have hβ : (Integral.CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel U.data.polarized.abelian hL).restrict q = β :=
    (Integral.FrameFactorization.IntegralLevelCover.fullFramePointsEquiv U.data.polarized.abelian hL (Over.mk f.left)).apply_symm_apply β
  refine ⟨Integral.PureAddedLevel.IntegralPureModel.frameToAddedMap (pureModel U) hL f q, ⟨(frameComparison U hL f q).trans
    (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.of_forgetAuxiliary e ?_)⟩⟩
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V c
  have h := congrArg (fun α : (U.data.polarized.abelian.pullback f.left).FullLevel L =>
    (α.hom.app (.op V) c).val ≫ e.polarized.abelian.hom) hβ
  exact h.trans (by
    change ((A.auxiliary.data.polarized.level.hom.app (.op V) c).val ≫
      e.polarized.abelian.inv) ≫ e.polarized.abelian.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

end IntegralPELFrame

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence
