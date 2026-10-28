import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineFiniteType
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameComparison

/-! # Models Reduced Common Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedCommonFrames.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iota : E →+* K}

theorem reducedPELLevelUnit (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (L : ℕ) [NeZero L]
    (x : (Reduction.reduction M.space).left) : IsUnit (L : (Reduction.reduction M.space).left.presheaf.stalk x) :=
  Integral.TwoLevelExistence.integer_unit_at_stalk_of_base_unit (Reduction.reduction M.space).hom L
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne L))) x

theorem reduced_finePEL_common_frames (κ : K →+* ℂ)
    {L : ℕ} [NeZero N] [NeZero L] (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (hN : 3 ≤ N) (hL : 3 ≤ L)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (A : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota L) (hA : A.IsFine)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ e : IntegralPEL.FrameExistence.IntegralPELFrame.space (Reduced.Iff.reducedPELUniversal M) (reducedPELLevelUnit M L) ≅
        IntegralPEL.FrameExistence.IntegralPELFrame.space (Reduced.Iff.reducedPELUniversal A) (reducedPELLevelUnit A N),
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso
        ((IntegralPEL.FrameExistence.IntegralPELFrame.universal (Reduced.Iff.reducedPELUniversal A) (reducedPELLevelUnit A N)).swap.pullback e.hom)
        (IntegralPEL.FrameExistence.IntegralPELFrame.universal (Reduced.Iff.reducedPELUniversal M) (reducedPELLevelUnit M L))) := by
  have : Countable K := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ K
  obtain ⟨hftM, _, hnM⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hN M hM hPresentations
  obtain ⟨hftA, _, hnA⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hL A hA hPresentations
  have : LocallyOfFiniteType (Reduction.reduction M.space).hom := hftM
  have : LocallyOfFiniteType (Reduction.reduction A.space).hom := hftA
  have : IsNoetherian (Reduction.reduction M.space).left := hnM
  have : IsNoetherian (Reduction.reduction A.space).left := hnA
  exact PEL.CommonFrameComparison.pel_common_frame_comparison (Reduced.Iff.reducedPELUniversal M) (Reduced.Iff.reducedPELUniversal A)
    (reducedPELLevelUnit M L) (reducedPELLevelUnit A N) hN hL hPresentations
    (Reduced.ActionClassification.reduced_finePEL_action_classifies M hM) (Reduced.ActionClassification.reduced_finePEL_action_classifies A hA)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedCommonFrames.FromPrimeModels
