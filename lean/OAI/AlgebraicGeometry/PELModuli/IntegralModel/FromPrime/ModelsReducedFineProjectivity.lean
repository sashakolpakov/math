import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverComplexProjectivity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFine
import OAI.RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation

/-! # Models Reduced Fine Projectivity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFineProjectivity.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem reduced_finePEL_complex_projective (h43 : ReferenceFamily.ModuliInput)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left
      (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom) := by
  have : NeZero N := ⟨by omega⟩
  have : Countable K := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ K
  obtain ⟨L, hL, _, A, hA, _, _, _, _, ⟨PA⟩, _, _, _⟩ :=
    ModelsDeepReference.FromPrimeModels.exists_deep_reference_geometry h43 hPresentations s hs hdegree P hP iota κ hemb N (by omega)
  have : NeZero L := ⟨by omega⟩
  have hadmissible := hP
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, hchain, _⟩ := hadmissible
  obtain ⟨hftM, _, hnM⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hN M hM hPresentations
  obtain ⟨hftA, _, hnA⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hL A hA hPresentations
  have : LocallyOfFiniteType (Reduction.reduction M.space).hom := hftM
  have : LocallyOfFiniteType (Reduction.reduction A.space).hom := hftA
  have : IsNoetherian (Reduction.reduction M.space).left := hnM
  have : IsNoetherian (Reduction.reduction A.space).left := hnA
  let B := Reduced.Iff.reducedPELUniversal A
  let u := IntegralPEL.FrameExistence.IntegralPELFrame.forget B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
  obtain ⟨hf, _, _⟩ := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_finite_etale_surjective B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
  have : IsFinite u.left := hf
  obtain ⟨q, hqf, hqt, hqs, _⟩ := PEL.CommonFrameProjection.common_frame_prescribed_projection
    (Reduced.Iff.reducedPELUniversal M) B (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit M L) (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit A N)
    hN hL hPresentations (Reduced.ActionClassification.reduced_finePEL_action_classifies M hM) (Reduced.ActionClassification.reduced_finePEL_action_classifies A hA)
  have : IsFinite q.left := hqf
  have : Etale q.left := hqt
  have : Surjective q.left := hqs
  let b := Spec.map (CommRingCat.ofHom κ)
  let F := Over.pullback b
  have : IsFinite (F.map u).left := MorphismProperty.of_isPullback (Specialization.base_change_square b u) hf
  have : IsFinite (F.map q).left := MorphismProperty.of_isPullback (Specialization.base_change_square b q) hqf
  have : Etale (F.map q).left := MorphismProperty.of_isPullback (Specialization.base_change_square b q) hqt
  have : Surjective (F.map q).left := MorphismProperty.of_isPullback (Specialization.base_change_square b q) hqs
  obtain ⟨hsm, hpr⟩ := ModelsReducedFine.FromPrimeModels.reduced_finePEL_smooth_proper h43 hPresentations
    s hs hdegree P hP iota κ hemb N hN M hM
  have : Smooth (Reduction.reduction M.space).hom := hsm
  have : IsProper (Reduction.reduction M.space).hom := hpr
  have : Smooth (F.obj (Reduction.reduction M.space)).hom :=
    inferInstanceAs (Smooth (pullback.snd (Reduction.reduction M.space).hom b))
  have : IsProper (F.obj (Reduction.reduction M.space)).hom :=
    inferInstanceAs (IsProper (pullback.snd (Reduction.reduction M.space).hom b))
  exact Finite.CoverComplexProjectivity.complex_target_projective_of_finite_flat_cover (F.map q)
    (RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation.finiteProjectivePresentation PA (F.map u))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFineProjectivity.FromPrimeModels
