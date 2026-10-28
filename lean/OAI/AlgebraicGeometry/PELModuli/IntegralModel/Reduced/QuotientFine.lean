import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientClassifyingMap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientFamilyUniqueness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackComparisonDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelExistence

/-! # Quotient Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! An actual polarized-action family recovering the prescribed
universal family is fine on all reduced tests. Neither parameter is
required to be reduced; the test families are actual integral PEL objects. Its classifiers are constructed from
prime-level covers, the family comparisons descend, and uniqueness is
proved on a common finite etale lift. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s p N : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsLocallyNoetherian Q.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hfib : U.ReducedQuotientFibers π)
    (A : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N Q.left)
    (e : PEL.Iso.PolarizedActionIso U.forgetAuxiliary.data (A.pullback π.left))

include hU hfib e in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotient_isFine (hp : p.Prime) (hunit : IsUnit (p : R))
    (hA : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ Q.left)
      (a : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.polarized.pullback t) (A.polarized.pullback t)),
      a.abelian.hom = 𝟙 (A.polarized.abelian.pullback t).scheme)
    (T : Over (Spec (.of R))) [IsReduced T.left] (C : PEL.Has.IntegralPELObject P R iotaO N T) :
    ∃! d : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback d.left) C.data) := by
  let hpT := Integral.TwoLevelExistence.integer_unit_at_stalk_of_base_unit T.hom p hunit
  obtain ⟨d, f, hd, ⟨c⟩⟩ := U.exists_reducedQuotient_classifying_map hU π hfib hp C hpT
  let q := IntegralPEL.FrameExistence.IntegralPELFrame.forget C hpT
  obtain ⟨hf, he, hs⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.finite_etale_surjective C hpT hp
  have : IsFinite q.left := hf
  have : Etale q.left := he
  have : Surjective q.left := hs
  let j : PEL.Iso.PolarizedActionIso ((A.pullback d.left).pullback q.left) (C.pullback q).data :=
    (PEL.Iso.PolarizedActionIso.pullbackComp A d.left q.left).trans
      ((PEL.Iso.PolarizedActionIso.pullbackCongr A _ _ (congrArg Over.Hom.left hd)).trans
        ((PEL.Iso.PolarizedActionIso.pullbackComp A π.left f.left).symm.trans
          ((e.symm.pullback f.left).trans c)))
  obtain ⟨a, _, _⟩ := PullbackComparisonDescent.pullback_pel_comparison_descends A hA d.left C.data q.left j
  refine ⟨d, ⟨a⟩, ?_⟩
  rintro g ⟨b⟩
  exact U.reducedQuotient_family_determines_map π hfib A e g d (b.trans a.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
