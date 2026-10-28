import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Data
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.PolarizationUniqueness

/-! # Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Realization.CM

noncomputable section

/-! Assemble the complete TateComparison one-step realization on the actual IntegralModel
spread, from the original fine-model correspondences and their proved
kernel classification. Group-map uniqueness is derived by cancellation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.PolarizationUniqueness

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Data.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
  (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
  [Smooth V.toOver.hom]

variable {r : ℕ} (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

theorem realizes
    (f : ∀ t : AbelianScheme.TateComparison.Local.IntegralType s, CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M (C t) t)
    (hf : ∀ t, CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M (C t) t χ (f t)) :
    (Data.CM.data M V D e C χ).RealizesIsogenyQuotient := by
  intro t
  let f' := Data.CM.isogeny M V D e C χ t (f t)
  refine ⟨f', Data.CM.kernel_geometry M V D e C χ t (f t) (hf t), ?_, ?_⟩
  · intro T _ x H
    exact Data.CM.classifies M V D e C χ t (f t) (hf t) T x H
  · intro p _ hp
    have : IsLocallyNoetherian (Data.CM.data M V D e C χ).space.left := Data.CM.space_noetherian M V
    have : Etale ((Data.CM.data M V D e C χ).correspondence t).source.left :=
      ((Data.CM.data M V D e C χ).correspondence t).etale
    have : IsLocallyNoetherian ((Data.CM.data M V D e C χ).correspondence t).cover.left :=
      LocallyOfFiniteType.isLocallyNoetherian ((Data.CM.data M V D e C χ).correspondence t).source.left
    exact CMExtraction.IsogenyQuotient.PolarizationUniqueness.polarization_unique_group_map f' p hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Realization.CM
