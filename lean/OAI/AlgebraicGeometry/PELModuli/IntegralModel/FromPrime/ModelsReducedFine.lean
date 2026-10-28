import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedCommonFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReferenceArithmetic
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProperDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSmoothAlgebraDescent

/-! # Models Reduced Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFine.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem reduced_finePEL_smooth_proper (h43 : ReferenceFamily.ModuliInput)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    Smooth (Reduction.reduction M.space).hom ∧ IsProper (Reduction.reduction M.space).hom := by
  have : NeZero N := ⟨by omega⟩
  have : Countable K := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ K
  obtain ⟨L, hL, _, A, hA, _, hsA, hpA, _, _, _⟩ :=
    ModelsDeepReferenceArithmetic.FromPrimeModels.exists_deep_smooth_proper_reference h43 hPresentations
      s hs hdegree P hP iota κ hemb N (by omega)
  have : NeZero L := ⟨by omega⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, hchain, _⟩ := hP
  obtain ⟨hftM, _, hnM⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hN M hM hPresentations
  obtain ⟨hftA, _, hnA⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hL A hA hPresentations
  have : LocallyOfFiniteType (Reduction.reduction M.space).hom := hftM
  have : LocallyOfFiniteType (Reduction.reduction A.space).hom := hftA
  have : IsNoetherian (Reduction.reduction M.space).left := hnM
  have : IsNoetherian (Reduction.reduction A.space).left := hnA
  have : IsProper (Reduction.reduction A.space).hom := hpA
  have : Smooth (Reduction.reduction A.space).hom := hsA
  let B := Reduced.Iff.reducedPELUniversal A
  let u := IntegralPEL.FrameExistence.IntegralPELFrame.forget B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
  obtain ⟨hf, ht, _⟩ := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_finite_etale_surjective B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
  have : IsFinite u.left := hf
  have : Etale u.left := ht
  have hsmooth : Smooth (IntegralPEL.FrameExistence.IntegralPELFrame.space B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)).hom := by
    rw [← u.w]
    infer_instance
  have hproper : IsProper (IntegralPEL.FrameExistence.IntegralPELFrame.space B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)).hom := by
    rw [← u.w]
    infer_instance
  obtain ⟨q, hqf, hqt, hqs, _⟩ := PEL.CommonFrameProjection.common_frame_prescribed_projection
    (Reduced.Iff.reducedPELUniversal M) B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit M L) (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
    hN hL hPresentations (Reduced.ActionClassification.reduced_finePEL_action_classifies M hM) (Reduced.ActionClassification.reduced_finePEL_action_classifies A hA)
  have : IsFinite q.left := hqf
  have : Etale q.left := hqt
  have : Surjective q.left := hqs
  have : IsProper (q.left ≫ (Reduction.reduction M.space).hom) := q.w.symm ▸ hproper
  have : Smooth (q.left ≫ (Reduction.reduction M.space).hom) := q.w.symm ▸ hsmooth
  exact ⟨Finite.EtaleSmoothAlgebraDescent.smooth_of_finite_etale_cover q.left (Reduction.reduction M.space).hom,
    Finite.CoverProperDescent.proper_of_finite_surjective_cover q.left (Reduction.reduction M.space).hom⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFine.FromPrimeModels
