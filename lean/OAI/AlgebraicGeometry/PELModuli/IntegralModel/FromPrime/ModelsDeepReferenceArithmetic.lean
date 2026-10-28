import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReference
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexSmoothProperDescent

/-! # Models Deep Reference Arithmetic -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReferenceArithmetic.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_deep_smooth_proper_reference (h43 : ReferenceFamily.ModuliInput)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 0 < N) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ L : ℕ, 3 ≤ L ∧ N ∣ L ∧ ∃ M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota L,
      M.IsFine ∧ M.HasProjectiveBallComponents κ ∧
      Smooth (Reduction.reduction M.space).hom ∧ IsProper (Reduction.reduction M.space).hom ∧
      Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left
        (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ)) ∧
      Finite (M.ComplexComponent κ) := by
  obtain ⟨L, hL, hNL, M, hM, hproj, _, hsC, hpC, hn, hr, hf, _⟩ :=
    ModelsDeepReference.FromPrimeModels.exists_deep_reference_geometry h43 hPresentations s hs hdegree P hP iota κ hemb N hN
  obtain ⟨hsK, hpK⟩ := ComplexSmoothProperDescent.smooth_proper_of_complex_baseChange κ (Reduction.reduction M.space) hsC hpC
  exact ⟨L, hL, hNL, M, hM, hproj, hsK, hpK, hn, hr, hf⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReferenceArithmetic.FromPrimeModels
