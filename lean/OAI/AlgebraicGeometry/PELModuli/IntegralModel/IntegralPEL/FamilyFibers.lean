import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId

/-! # Family Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FamilyFibers

noncomputable section

/-! A comparison with a family on the base canonically identifies
its two pullbacks along maps with equal base maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y T : Over (Spec (.of R))}

def prescribedFamilyPullbackComparison (A : PEL.Has.IntegralPELObject P R iotaO N Y)
    (U : PEL.Has.IntegralPELObject P R iotaO N X) (q : X ⟶ Y)
    (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.data) (f : T ⟶ X) :
    PEL.Iso.PolarizedActionIso (A.pullback (f ≫ q)).data (U.pullback f).data :=
  (PEL.Iso.PolarizedActionIso.pullbackComp A.data q.left f.left).symm.trans (e.pullback f.left)

def prescribedFamilyFiberComparison (A : PEL.Has.IntegralPELObject P R iotaO N Y)
    (U : PEL.Has.IntegralPELObject P R iotaO N X) (q : X ⟶ Y)
    (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.data) (f g : T ⟶ X)
    (h : f ≫ q = g ≫ q) : PEL.Iso.PolarizedActionIso (U.pullback f).data (U.pullback g).data :=
  (prescribedFamilyPullbackComparison A U q e f).symm.trans
    ((PEL.Iso.PolarizedActionIso.pullbackCongr A.data _ _ (congrArg Over.Hom.left h)).trans
      (prescribedFamilyPullbackComparison A U q e g))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FamilyFibers
