import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReference
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedCommonFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Generic
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameAffineTransfer

/-! # Reduced Fine Complex Affine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineComplexAffine.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem reduced_finePEL_complex_affine (h43 : ReferenceFamily.ModuliInput)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    IsReduced (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left ∧
    (∀ F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left, F.Finite →
      ∃ V : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen V ∧ F ⊆ V) := by
  have : NeZero N := ⟨by omega⟩
  have : Countable K := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ K
  obtain ⟨L, hL, _, B, hB, _, _, hsB, hpB, _, _, _, hAF⟩ :=
    ModelsDeepReference.FromPrimeModels.exists_deep_reference_geometry h43 hPresentations s hs hdegree P hP iota κ hemb N (by omega)
  have : NeZero L := ⟨by omega⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, hchain, _⟩ := hP
  obtain ⟨hftM, _, hnM⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hN M hM hPresentations
  obtain ⟨hftB, _, hnB⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hL B hB hPresentations
  have : LocallyOfFiniteType (Reduction.reduction M.space).hom := hftM
  have : LocallyOfFiniteType (Reduction.reduction B.space).hom := hftB
  have : IsNoetherian (Reduction.reduction M.space).left := hnM
  have : IsNoetherian (Reduction.reduction B.space).left := hnB
  have : Smooth (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).hom := hsB
  have : IsProper (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).hom := hpB
  have hred : IsReduced (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).left :=
    AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smoothOverField_isReduced (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).hom
  have hsep : (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (Reduced.ReducedComplexPEL.reducedComplexPEL B κ).hom]
    infer_instance⟩
  exact PEL.CommonFrameAffineTransfer.common_frame_affine_transfer (Reduced.Iff.reducedPELUniversal M) (Reduced.Iff.reducedPELUniversal B)
    (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit M L) (ModelsReducedCommonFrames.FromPrimeModels.reducedPELLevelUnit B N) hN hL hPresentations
    (Reduced.ActionClassification.reduced_finePEL_action_classifies M hM) (Reduced.ActionClassification.reduced_finePEL_action_classifies B hB) κ
    (Reduced.Generic.reduced_generic_finePEL_action_classifies κ M hM) hred hsep hAF

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineComplexAffine.FromPrimeModels
