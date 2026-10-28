import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Iff

/-! # Action Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionClassification

noncomputable section

/-! The given reduced universal PEL family classifies through actual
polarized action isomorphisms over the original number field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iota : E →+* K} (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

theorem reduced_finePEL_action_classifies (hM : M.IsFine)
    (Y : Over (Spec (.of K))) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P K
      (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Y) :
    ∃! f : Y ⟶ Reduction.reduction M.space,
      Nonempty (PEL.Iso.PolarizedActionIso ((Iff.reducedPELUniversal M).pullback f).data A.data) := by
  obtain ⟨f, ⟨e⟩, hu⟩ := Iff.reduced_finePEL_classifies M hM Y A
  refine ⟨f, ⟨e.toActionIso.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data)⟩, ?_⟩
  rintro g ⟨a⟩
  exact hu g ⟨PEL.Has.PulledBackPELDataIso.ofActionIso
    (a.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionClassification
