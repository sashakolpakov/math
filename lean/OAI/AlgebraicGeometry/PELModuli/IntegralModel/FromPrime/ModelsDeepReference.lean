import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedProjective

/-! # Models Deep Reference -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReference.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_deep_reference_geometry (h43 : ReferenceFamily.ModuliInput)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 0 < N) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ L : ℕ, 3 ≤ L ∧ N ∣ L ∧ ∃ M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota L,
      M.IsFine ∧ M.HasProjectiveBallComponents κ ∧
      IsNoetherian (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left ∧
      Smooth (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom ∧ IsProper (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom ∧
      Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left
        (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ)) ∧
      Finite (M.ComplexComponent κ) ∧
      (∀ (F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left), F.Finite →
        ∃ U : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen U ∧ F ⊆ U) := by
  obtain ⟨L, hL, hNL, M, hM, hproj⟩ :=
    ReferenceFamily.exists_deep_projective_reference h43 s hs hdegree P hP iota κ hemb N hN
  have : NeZero L := ⟨by omega⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, hchain, _⟩ := hP
  exact ⟨L, hL, hNL, M, hM, hproj,
    ModelsReducedProjective.FromPrimeModels.reduced_projectivePEL_complex_geometry κ P hs hδ hchain iota hL M hM hproj hPresentations⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsDeepReference.FromPrimeModels
