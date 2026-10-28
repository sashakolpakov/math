import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback

/-! # Fine Data Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineDataReduction

noncomputable section

/-! Classification on reduced tests passes to the actual reduction of
the parameter. The universal polarized-action family is its actual
pullback along the nilradical closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem polarizedAction_classifies_reduction
    (A : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N X.left)
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback f.left) B.data))
    (T : Over (Spec (.of R))) [IsReduced T.left] (B : PEL.Has.IntegralPELObject P R iotaO N T) :
    ∃! f : T ⟶ Reduction.reduction X,
      Nonempty (PEL.Iso.PolarizedActionIso
        ((A.pullback (Reduction.reductionι X).left).pullback f.left) B.data) := by
  obtain ⟨d, ⟨e⟩, hu⟩ := hA T B
  let f := Reduction.factorToReduction d
  have hf : f ≫ Reduction.reductionι X = d := Reduction.factorToReduction_ι d
  refine ⟨f, ⟨(PEL.Iso.PolarizedActionIso.pullbackComp A (Reduction.reductionι X).left f.left).trans
    ((PEL.Iso.PolarizedActionIso.pullbackCongr A _ _ (congrArg Over.Hom.left hf)).trans e)⟩, ?_⟩
  rintro g ⟨a⟩
  apply (cancel_mono (Reduction.reductionι X)).mp
  have hg := hu (g ≫ Reduction.reductionι X)
    ⟨(PEL.Iso.PolarizedActionIso.pullbackComp A (Reduction.reductionι X).left g.left).symm.trans a⟩
  exact hg.trans hf.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineDataReduction
