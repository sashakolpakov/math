import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfConditions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback

/-! # Object After Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ObjectAfterBaseChange

noncomputable section

section

/-! Rosati compatibility known on an actual fppf cover holds after
any base change to a reduced noetherian scheme. The proof compares the
two iterated pullbacks on the literal cartesian cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem rosati_after_baseChange_of_cover
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S T V : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PEL.Has.PolarizedActionData E g δ N S)
    (u : T ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (h : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback u).polarized (A.pullback u).action)
    (f : V ⟶ S) [IsReduced V] [IsNoetherian V] :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback f).polarized (A.pullback f).action := by
  let p := pullback.fst u f
  let q := pullback.snd u f
  let e : PEL.Iso.PolarizedActionIso ((A.pullback u).pullback p) ((A.pullback f).pullback q) :=
    (PEL.Iso.PolarizedActionIso.pullbackComp A u p).trans
      ((PEL.Iso.PolarizedActionIso.pullbackCongr A (p ≫ u) (q ≫ f) pullback.condition).trans
        (PEL.Iso.PolarizedActionIso.pullbackComp A f q).symm)
  apply FppfConditions.rosati_of_fppf_baseChange q (A.pullback f).polarized (A.pullback f).action
  exact RosatiIsoTransport.rosati_of_polarized_iso e.polarized ((A.pullback u).pullback p).action
    ((A.pullback f).pullback q).action (fun r => (e.action r).symm)
    (PEL.BaseChange.rosati_pullback (A.pullback u).polarized (A.pullback u).action h p)

end

/-! An actual polarized family with its integral action becomes an
integral PEL object after reduced noetherian base change when its Rosati
equations are verified on an actual fppf cover and its Lie ranks hold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R}

def integralPELObjectAfterBaseChange {X Y : Over (Spec (.of R))}
    (A : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N X.left)
    {V : Scheme.{0}} (u : V ⟶ X.left) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (hrosati : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback u).polarized (A.pullback u).action)
    (hlie : PEL.Has.HasIntegralLieRanks P R iotaO X A.polarized.abelian A.action)
    (f : Y ⟶ X) [IsReduced Y.left] [IsNoetherian Y.left] : PEL.Has.IntegralPELObject P R iotaO N Y where
  data := A.pullback f.left
  rosati := rosati_after_baseChange_of_cover A u hrosati f.left
  lieRanks := PEL.BaseChange.integralLieRanks_pullback A.polarized.abelian A.action hlie f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ObjectAfterBaseChange
