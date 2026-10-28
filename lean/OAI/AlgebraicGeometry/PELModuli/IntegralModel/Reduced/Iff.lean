import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Iff -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Iff

noncomputable section

/-!
The actual reduction of a characteristic-zero fine PEL space represents
the PEL problem on reduced test schemes. Its universal family is constructed
by pullback. Classification uses the same geometric family-isomorphism
predicate as the integral IntegralModel target, including action, polarization,
Poincare bundle, and full level.

This is the reduced characteristic-zero model. Spreading its representing
property to a localized ring of integers remains a separate construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {K : Type} [Field K] [NumberField K] {iota : E →+* K}

/-- The universal PEL object on the nilradical reduction is an actual
pullback, with the Rosati and geometric Lie-rank conditions proved. -/
abbrev reducedPELUniversal (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) :
    PEL.Has.IntegralPELObject P K (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N
      (Reduction.reduction M.space) :=
  (PEL.BaseChange.integralPELOfCharacteristicZero M.universal).pullback (Reduction.reductionι M.space)

/-- Classification on the reduction agrees with ReferenceFamily classification after
composition with its closed inclusion. This compares actual families. -/
theorem reducedPEL_classifying_iff (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    {Y : Over (Spec (.of K))}
    (A : PEL.Has.IntegralPELObject P K
      (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Y)
    (f : Y ⟶ Reduction.reduction M.space) :
    Nonempty (PEL.Has.PulledBackPELDataIso (reducedPELUniversal M).data A.data f.left (𝟙 Y.left)) ↔
      Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal A.toCharacteristicZero
        (f ≫ Reduction.reductionι M.space)) := by
  let U := PEL.Has.characteristicZeroPELData P M.universal
  constructor
  · rintro ⟨e⟩
    apply Nonempty.intro
    apply PEL.Iso.pelPullbackOfActionIso
    exact ((PEL.Iso.PolarizedActionIso.pullbackComp U (Reduction.reductionι M.space).left f.left).symm.trans
      (e.toActionIso.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data))).symm
  · rintro ⟨e⟩
    apply Nonempty.intro
    apply PEL.Has.PulledBackPELDataIso.ofActionIso
    exact (PEL.Iso.PolarizedActionIso.pullbackComp U (Reduction.reductionι M.space).left f.left).trans
      ((PEL.Iso.actionIsoOfPELPullback e).symm.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)

/-- The reduced fine-moduli property over the number field is proved from
ReferenceFamily's actual fine-moduli property; it is not added as a model assumption. -/
theorem reduced_finePEL_classifies (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (Y : Over (Spec (.of K))) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P K
      (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Y) :
    ∃! f : Y ⟶ Reduction.reduction M.space,
      Nonempty (PEL.Has.PulledBackPELDataIso (reducedPELUniversal M).data A.data
        f.left (𝟙 Y.left)) := by
  obtain ⟨f, hf, huniq⟩ := hM Y A.toCharacteristicZero
  refine ⟨Reduction.factorToReduction f, ?_, ?_⟩
  · apply (reducedPEL_classifying_iff M A _).mpr
    simpa only [Reduction.factorToReduction_ι] using hf
  · intro g hg
    apply (cancel_mono (Reduction.reductionι M.space)).mp
    rw [Reduction.factorToReduction_ι]
    exact huniq _ ((reducedPEL_classifying_iff M A g).mp hg)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Iff
