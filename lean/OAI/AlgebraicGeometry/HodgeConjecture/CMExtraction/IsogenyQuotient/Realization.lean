import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenKernels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.PolarizationUniqueness

/-! # Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Realization

noncomputable section

/-! Assemble the TateComparison realization on exactly the retained IntegralModel model.
The correspondence family is constructed from the original fine model;
polarization uniqueness is proved by cancellation on its Noetherian cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (I : RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.IntegralModel P iota κ M)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

theorem retained_realizes
    (f : ∀ t : AbelianScheme.TateComparison.Local.IntegralType s, FineKernelData.UniversalIsogeny (q := q) M (C t) t)
    (hf : ∀ t, FineKernelData.ClassifiesChosenKernels M (C t) t χ (f t)) :
    (I.heckeData (fun t => Correspondence.retainedFineCorrespondence I (C t)) χ).RealizesIsogenyQuotient := by
  let D := I.heckeData (fun t => Correspondence.retainedFineCorrespondence I (C t)) χ
  change D.RealizesIsogenyQuotient
  intro t
  let f' : D.UniversalIsogeny t := Correspondence.retainedUniversalIsogeny I (C t) t (f t)
  refine ⟨f', ?_, ?_, ?_⟩
  · exact ChosenKernels.IsogenyQuotient.retained_kernel_geometry I (C t) t χ (f t) (hf t)
  · intro T _ x F
    exact ChosenKernels.IsogenyQuotient.retained_kernel_classification I (C t) t χ (f t) (hf t) T x F
  · intro p hmon hp
    let : IsFinite (Correspondence.retainedFineCorrespondence I (C t)).source.left :=
      (Correspondence.retainedFineCorrespondence I (C t)).finite
    have hnoeth : IsLocallyNoetherian (Correspondence.retainedFineCorrespondence I (C t)).cover.left :=
      LocallyOfFiniteType.isLocallyNoetherian (Correspondence.retainedFineCorrespondence I (C t)).source.left
    exact @PolarizationUniqueness.polarization_unique_group_map _ _ _ hnoeth _ _ _
      (D.sourceFamily t) (D.targetFamily t) f' p hmon hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Realization
