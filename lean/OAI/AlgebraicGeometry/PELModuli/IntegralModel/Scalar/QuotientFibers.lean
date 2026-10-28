import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientFiberCondition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange

/-! # Quotient Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed quotient fiber relation survives arbitrary
coefficient change. The proof uses the original kernel-pair relation and
the native family pullback comparisons on the same reduced test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (φ : R →+* R')

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPrescribedComparison {T : Over (Spec (.of R'))}
    (f : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) :
    PEL.Iso.PolarizedActionIso (((U.baseChange φ).forgetAuxiliary).pullback f).data
      (U.forgetAuxiliary.pullback (Scalar.Line.scalarOriginalMap (Spec.map (CommRingCat.ofHom φ)) f)).data :=
  PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) f.left

theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotientFibers_baseChange (π : X ⟶ Q) (hfib : U.ReducedQuotientFibers π) :
    (U.baseChange φ).ReducedQuotientFibers
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π) := by
  intro T _ f g
  let b := Spec.map (CommRingCat.ofHom φ)
  have : IsReduced ((Over.map b).obj T).left := inferInstanceAs (IsReduced T.left)
  rw [Scalar.Line.scalarQuotient_eq_iff b π f g, hfib ((Over.map b).obj T)]
  constructor
  · rintro ⟨e⟩
    exact ⟨(U.scalarPrescribedComparison φ f).trans (e.trans (U.scalarPrescribedComparison φ g).symm)⟩
  · rintro ⟨e⟩
    exact ⟨(U.scalarPrescribedComparison φ f).symm.trans (e.trans (U.scalarPrescribedComparison φ g))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
