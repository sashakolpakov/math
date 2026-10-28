import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Classification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

/-! # Fine Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineReduction

noncomputable section

/-! Reducing a two-level parameter retains its actual universal PEL
family and its classification on every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem integralAddedPEL_fine_reduction (U : PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hU : U.IsFine) : (U.pullback (Reduction.reductionι X)).IsFine := by
  intro T _ A
  obtain ⟨f, ⟨e⟩, hu⟩ := hU T A
  let g := Reduction.factorToReduction f
  have hg : g ≫ Reduction.reductionι X = f := Reduction.factorToReduction_ι f
  refine ⟨g, ⟨(U.pullbackCompIso (Reduction.reductionι X) g).trans
    ((U.pullbackCongrIso _ _ hg).trans e)⟩, ?_⟩
  rintro h ⟨a⟩
  apply (cancel_mono (Reduction.reductionι X)).mp
  exact (hu (h ≫ Reduction.reductionι X) ⟨(U.pullbackCompIso (Reduction.reductionι X) h).symm.trans a⟩).trans hg.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineReduction
