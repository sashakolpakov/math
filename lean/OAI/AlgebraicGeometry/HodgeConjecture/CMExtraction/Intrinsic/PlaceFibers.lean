import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.PlaceFibers
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta

/-! # Place Fibers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PlaceFibers.ParameterChoices

noncomputable section

/-! The actual native CM slots above one real-subfield place are
exactly its two conjugate labels. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.PlaceFibers.Approximation OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta.Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem nativeFieldEmbedding_injective (hq : D.IsGoodCompletelySplitPrime) :
    Function.Injective (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) := by
  intro i j h
  apply GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding_injective D hq
  ext x
  exact RingHom.congr_fun h x

variable [IsGalois ℚ E]

theorem native_cmActivePlace_fiber (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (i j : Fin s × Bool) :
    CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i) = CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D j) ↔
      i.1 = j.1 := by
  constructor
  · intro h
    rcases (CM.PlaceFibers.Approximation.cmActivePlace_eq_iff E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D j)
      D.reference.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E D.reference hg.reference_admissible)
      (OneTheta.Multiplicity.nativeOneDeltaNonzero E D.reference hg.reference_admissible)).mp h with he | he
    · exact congrArg Prod.fst (nativeFieldEmbedding_injective E D hq he)
    · have he' : LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (j.1, !j.2) :=
        he.trans (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq j.1 j.2).symm
      have hi : i = (j.1, !j.2) := nativeFieldEmbedding_injective E D hq he'
      have hip := congrArg (fun k : Fin s × Bool => k.1) hi
      exact hip
  · rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    intro h
    change i = j at h
    subst j
    have hc (side : Bool) : CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (i, !side)) =
        CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (i, side)) := by
      rw [GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq i side, CM.PlaceFibers.Approximation.cmActivePlace_conjugate]
    cases a <;> cases b
    · rfl
    · exact hc true
    · exact hc false
    · rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PlaceFibers.ParameterChoices
